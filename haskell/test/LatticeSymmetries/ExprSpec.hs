{-# LANGUAGE OverloadedLists #-}

module LatticeSymmetries.ExprSpec (spec) where

import Control.Exception (bracket)
import Data.Aeson qualified as Aeson
import Data.ByteString (packCString, useAsCString)
import Foreign (fromBool)
import Foreign.C (CString)
import LatticeSymmetries.Algebra
import LatticeSymmetries.Automorphisms
import LatticeSymmetries.ComplexRational (ComplexRational (ComplexRational))
import LatticeSymmetries.Expr
import LatticeSymmetries.Generator
import LatticeSymmetries.NonbranchingTerm (HasNonbranchingRepresentation (nonbranchingRepresentation))
import LatticeSymmetries.Some
import LatticeSymmetries.Utils (decodeCString, ls_hs_destroy_string, toPrettyText)
import Test.Hspec
import Test.Hspec.QuickCheck
import Utils
import Prelude hiding (Product, Sum)

import Data.Text.IO qualified
import Data.Text.IO qualified as Text.IO

decodeCexprResult :: IO CString -> IO SomeExpr
decodeCexprResult action =
  bracket action ls_hs_destroy_string $ \cStr ->
    bracket (extractRight =<< extractRight =<< decodeCString @(Either Text _) cStr) ls_hs_destroy_expr $ foldCexpr pure

spec :: Spec
spec = do
  describe "ls_hs_expr_from_json / ls_hs_expr_to_json" $ do
    modifyMaxSize (const 100) $ prop "round trips" $ \(someExpr :: SomeExpr) ->
      useAsCString (toStrict (Aeson.encode someExpr)) $ \exprEncoded ->
        bracket (ls_hs_expr_from_json exprEncoded) ls_hs_destroy_string $ \cExprStr -> do
          cExpr <- extractRight =<< extractRight =<< decodeCString @(Either Text _) cExprStr
          bracket (ls_hs_expr_to_json cExpr) ls_hs_destroy_string $ \cStr -> do
            Just e <- Aeson.decodeStrict <$> packCString cStr
            when (mapSomeExpr simplifyExpr someExpr /= e) $ do
              Text.IO.putStrLn $ toPrettyText (mapSomeExpr simplifyExpr someExpr) <> " | " <> toPrettyText e
            e `shouldBe` mapSomeExpr simplifyExpr someExpr
  -- it "simplifies expressions upon construction" $ do
  --   let s = "(0.25 σ⁺_0 (I - σᶻ_1) (I - σᶻ_0) + 0.3535533905932738 σ⁺_1 σ⁻_0 (I - σᶻ_1) (I + σᶻ_0) + 0.4330127018922193 σ⁺_0 (I + σᶻ_1) (I - σᶻ_0))"
  --       jsonString = "{\"expression\":\"" <> s <> "\"}"
  --   e <- extractRight $ mkExpr SpinTag s
  --   Data.Text.IO.putStrLn jsonString
  --   useAsCString (encodeUtf8 jsonString) $ \exprEncoded ->
  --     bracket (ls_hs_expr_from_json exprEncoded) ls_hs_destroy_string $ \cExprStr -> do
  --       cExpr <- extractRight =<< extractRight =<< decodeCString @(Either Text _) cExprStr
  --       print @SomeExpr cExpr
  --   toPrettyText e `shouldBe` ""

  describe "ls_hs_expr_to_string" $ do
    prop "pretty prints" $ \(someExpr :: SomeExpr) ->
      bracket (newCexpr someExpr) ls_hs_destroy_expr $ \cExpr ->
        bracket (ls_hs_expr_to_string cExpr) ls_hs_destroy_string $ \cStr ->
          decodeUtf8 <$> packCString cStr `shouldReturn` toPrettyText someExpr
  describe "Num" $ do
    let check :: (IsBasis t, Show (Expr t)) => ParticleTag t -> Expr t -> Expr t -> Expr t -> Expectation
        check _tag a b c = do
          simplifyExpr (negate (simplifyExpr (negate a))) `shouldBe` simplifyExpr a
          simplifyExpr (a + b) `shouldBe` simplifyExpr (b + a)
          simplifyExpr (a - b) `shouldBe` simplifyExpr (negate (b - a))
          simplifyExpr (simplifyExpr (a + b) + c) `shouldBe` simplifyExpr (a + simplifyExpr (b + c))
          simplifyExpr (simplifyExpr (a + b) * c) `shouldBe` simplifyExpr (a * c + b * c)
    prop "SpinTy" $ check SpinTag
    prop "SpinlessFermionTy" $ check SpinlessFermionTag
    prop "SpinfulFermionTy" $ check SpinfulFermionTag
  describe "ls_hs_{plus,minus,times,scale}" $ do
    let check :: (IsBasis t, Show (Expr t)) => ParticleTag t -> Expr t -> Expr t -> Expectation
        check tag a b = do
          bracket (newCexpr (SomeExpr tag a)) ls_hs_destroy_expr $ \cA ->
            bracket (newCexpr (SomeExpr tag b)) ls_hs_destroy_expr $ \cB -> do
              ls_hs_expr_equal cA cA `shouldReturn` fromBool True
              ls_hs_expr_equal cB cB `shouldReturn` fromBool True
              decodeCexprResult (ls_hs_expr_plus cA cB) `shouldReturn` SomeExpr tag (simplifyExpr (a + b))
              decodeCexprResult (ls_hs_expr_minus cA cB) `shouldReturn` SomeExpr tag (simplifyExpr (a - b))
              decodeCexprResult (ls_hs_expr_times cA cB) `shouldReturn` SomeExpr tag (simplifyExpr (a * b))
              bracket (ls_hs_expr_negate cA) ls_hs_destroy_expr $
                foldCexpr (`shouldBe` SomeExpr tag (-a))
              bracket (ls_hs_expr_scale 2.0 (-5.0) cA) ls_hs_destroy_expr $
                foldCexpr (`shouldBe` SomeExpr tag (ComplexRational 2 (-5) `scale` a))
    prop "SpinTy" $ check SpinTag
    prop "SpinlessFermionTy" $ check SpinlessFermionTag
    prop "SpinfulFermionTy" $ check SpinfulFermionTag
  describe "exprPermutationGroup" $ do
    it "computes permutation groups" $ do
      e1 <- extractRight $ mkExpr SpinTag "2 (σ⁺₀ σ⁻₁ + σ⁺₁ σ⁻₀) + σᶻ₀ σᶻ₁"
      (exprPermutationGroup Nothing e1).permutations `shouldBe` [[0, 1], [1, 0]]
      e2 <- extractRight $ mkExpr SpinTag "2 I + S+3"
      (exprPermutationGroup Nothing e2).permutations
        `shouldBe` [[0, 1, 2, 3], [0, 2, 1, 3], [1, 0, 2, 3], [1, 2, 0, 3], [2, 0, 1, 3], [2, 1, 0, 3]]
      e3 <- extractRight $ mkExpr SpinTag "S+0 S-1 + S+1 S-0"
      (exprPermutationGroup Nothing e3).permutations
        `shouldBe` [[0, 1], [1, 0]]
      e4 <- extractRight $ mkExpr SpinTag "2 (σ⁺0 σ⁻1 + σ⁺1 σ⁻0) + σᶻ0 σᶻ1 + 2 (σ⁺1 σ⁻2 + σ⁺2 σ⁻1) + σᶻ1 σᶻ2 + 2 (σ⁺2 σ⁻0 + σ⁺0 σ⁻2) + σᶻ2 σᶻ0"
      (exprPermutationGroup Nothing e4).permutations
        `shouldBe` [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]]
  describe "HasNonbranchingRepresentation" $ do
    prop "identities match" $ do
      nonbranchingRepresentation (Generator (1 :: Int) SpinIdentity)
        `shouldBe` nonbranchingRepresentation (Generator (2 :: Int) FermionIdentity)
  describe "isInvariantUponSpinInversion" $ do
    it "works for SpinTy" $ do
      isInvariantUponSpinInversion <$> mkExpr SpinTag "2 (σ⁺₀ σ⁻₁ + σ⁺₁ σ⁻₀) + σᶻ₀ σᶻ₁"
        `shouldBe` Right True
      isInvariantUponSpinInversion <$> mkExpr SpinTag "σ⁺₀ σ⁻₁"
        `shouldBe` Right False
      isInvariantUponSpinInversion <$> mkExpr SpinTag "σᶻ₁"
        `shouldBe` Right False
      isInvariantUponSpinInversion <$> mkExpr SpinTag "S^x_10"
        `shouldBe` Right True
  describe "conservesNumberParticles" $ do
    it "works for SpinTy" $ do
      toPrettyText <$> mkExpr SpinTag "σ⁺₀ σ⁻₀" `shouldBe` Right "0.5 I + 0.5 σᶻ₀"
      toPrettyText <$> mkExpr SpinTag "σ⁻₀ σ⁺₀" `shouldBe` Right "0.5 I - 0.5 σᶻ₀"
      toPrettyText <$> mkExpr SpinTag "σᶻ₀ σ⁻₀ σ⁺₁" `shouldBe` Right "-σ⁻₀ σ⁺₁"
      toPrettyText <$> mkExpr SpinTag "σᶻ₁ σ⁺₁" `shouldBe` Right "σ⁺₁"
      toPrettyText <$> mkExpr SpinTag "σ⁺₁ σᶻ₁" `shouldBe` Right "-σ⁺₁"
      toPrettyText <$> mkExpr SpinTag "σᶻ₁ σ⁻₀ σ⁺₁" `shouldBe` Right "σ⁻₀ σ⁺₁"
      toPrettyText <$> mkExpr SpinTag "σᶻ₀ σ⁺₀ σ⁻₁" `shouldBe` Right "σ⁺₀ σ⁻₁"
      toPrettyText <$> mkExpr SpinTag "σᶻ₁ σ⁺₀ σ⁻₁" `shouldBe` Right "-σ⁺₀ σ⁻₁"
      -- e <- extractRight $ mkExpr SpinTag "2 (σ⁺₀ σ⁻₁ + σ⁺₁ σ⁻₀) + σᶻ₀ σᶻ₁"
      -- m <- extractRight $ mkExpr SpinTag "σᶻ₀ + σᶻ₁"
      -- Text.IO.putStrLn $ toPrettyText e
      -- Text.IO.putStrLn $ toPrettyText m
      -- Text.IO.putStrLn $ toPrettyText (e * m)
      -- Text.IO.putStrLn $ toPrettyText (m * e)
      conservesNumberParticles <$> mkExpr SpinTag "2 (σ⁺₀ σ⁻₁ + σ⁺₁ σ⁻₀) + σᶻ₀ σᶻ₁"
        `shouldBe` Right True
      conservesNumberParticles <$> mkExpr SpinTag "σᶻ₀ σᶻ₁"
        `shouldBe` Right True
      conservesNumberParticles <$> mkExpr SpinTag "2 (σ⁺₀ σ⁻₁ + σ⁺₁ σ⁻₀)"
        `shouldBe` Right True
      conservesNumberParticles <$> mkExpr SpinTag "σ⁺₀ σ⁺₁ + σ⁻₁ σ⁻₀"
        `shouldBe` Right False
  describe "simplifyExpr" $ do
    it "works for big expressions" $ do
      let e1 = "(0.25 σ⁺_0 (I - σᶻ_1) (I - σᶻ_0) + 0.3535533905932738 σ⁺_1 σ⁻_0 (I - σᶻ_1) (I + σᶻ_0) + 0.4330127018922193 σ⁺_0 (I + σᶻ_1) (I - σᶻ_0))"
          e2 = "(0.25 (I - σᶻ_0) (I - σᶻ_1) σ⁻_0 + 0.3535533905932738 (I - σᶻ_1) (I + σᶻ_0) σ⁺_0 σ⁻_1 + 0.4330127018922193 (I - σᶻ_0) (I + σᶻ_1) σ⁻_0)"
          s = e1 <> " " <> e1 <> " " <> e2 <> " " <> e2
      print $ mkExpr SpinTag s
      True `shouldBe` True
