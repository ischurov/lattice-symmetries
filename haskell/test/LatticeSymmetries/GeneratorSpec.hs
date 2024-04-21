module LatticeSymmetries.GeneratorSpec (spec) where

import Data.Aeson qualified as Aeson
import Data.Bits
import LatticeSymmetries.BitString
import LatticeSymmetries.Generator
import LatticeSymmetries.NonbranchingTerm
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck
import Utils

instance Arbitrary (BasisState t) where
  arbitrary = do
    n <- chooseInt (1, 500)
    bits <- fromInteger <$> chooseInteger (0, bit n - 1)
    pure $ BasisState n (BitString bits)

spec :: Spec
spec = do
  describe "ParticleTy" $ do
    it "FromJSON works" $ do
      Aeson.decode "\"spin\"" `shouldBe` Just SpinTy
      Aeson.decode "\"spinless-fermion\"" `shouldBe` Just SpinlessFermionTy
      Aeson.decode "\"spinful-fermion\"" `shouldBe` Just SpinfulFermionTy
  describe "ToJSON / FromJSON (ParticleTy, SpinGeneratorType, FermionGeneratorType)" $ do
    prop "ParticleTy" $ shouldRoundTrip @ParticleTy
  describe "BasisState" $ do
    prop "invertBasisState" $ \x@(BasisState n bits) -> do
      let y@(BasisState n' bits') = invertBasisState x
      n' `shouldBe` n
      (bits' Data.Bits..&. bits) `shouldBe` zeroBits
      invertBasisState y `shouldBe` x
  describe "HasNonbranchingRepresentation" $ do
    it "SpinTy" $ do
      -- SpinIdentity
      -- 1 0
      -- 0 1
      nonbranchingRepresentation SpinIdentity `actOnKet` BitString 0b0 `shouldBe` (1, BitString 0b0)
      nonbranchingRepresentation SpinIdentity `actOnKet` BitString 0b1 `shouldBe` (1, BitString 0b1)
      BitString 0b0 `actOnBra` nonbranchingRepresentation SpinIdentity `shouldBe` (1, BitString 0b0)
      BitString 0b1 `actOnBra` nonbranchingRepresentation SpinIdentity `shouldBe` (1, BitString 0b1)
      -- SpinZ
      -- 1  0
      -- 0 -1
      nonbranchingRepresentation SpinZ `actOnKet` BitString 0b0 `shouldBe` (1, BitString 0b0)
      nonbranchingRepresentation SpinZ `actOnKet` BitString 0b1 `shouldBe` (-1, BitString 0b1)
      BitString 0b0 `actOnBra` nonbranchingRepresentation SpinZ `shouldBe` (1, BitString 0b0)
      BitString 0b1 `actOnBra` nonbranchingRepresentation SpinZ `shouldBe` (-1, BitString 0b1)
      -- SpinPlus
      -- 0 1
      -- 0 0
      nonbranchingRepresentation SpinPlus `actOnKet` BitString 0b0 `shouldBe` (0, BitString 0b0)
      nonbranchingRepresentation SpinPlus `actOnKet` BitString 0b1 `shouldBe` (1, BitString 0b0)
      BitString 0b0 `actOnBra` nonbranchingRepresentation SpinPlus `shouldBe` (1, BitString 0b1)
      BitString 0b1 `actOnBra` nonbranchingRepresentation SpinPlus `shouldBe` (0, BitString 0b1)
      -- SpinMinus
      -- 0 0
      -- 1 0
      nonbranchingRepresentation SpinMinus `actOnKet` BitString 0b0 `shouldBe` (1, BitString 0b1)
      nonbranchingRepresentation SpinMinus `actOnKet` BitString 0b1 `shouldBe` (0, BitString 0b1)
      BitString 0b0 `actOnBra` nonbranchingRepresentation SpinMinus `shouldBe` (0, BitString 0b0)
      BitString 0b1 `actOnBra` nonbranchingRepresentation SpinMinus `shouldBe` (1, BitString 0b0)
      -- InternalSpinMinusPlus
      -- 0 0
      -- 0 1
      nonbranchingRepresentation InternalSpinMinusPlus `actOnKet` BitString 0b0 `shouldBe` (0, BitString 0b0)
      nonbranchingRepresentation InternalSpinMinusPlus `actOnKet` BitString 0b1 `shouldBe` (1, BitString 0b1)
      BitString 0b0 `actOnBra` nonbranchingRepresentation InternalSpinMinusPlus `shouldBe` (0, BitString 0b0)
      BitString 0b1 `actOnBra` nonbranchingRepresentation InternalSpinMinusPlus `shouldBe` (1, BitString 0b1)
      -- InternalSpinPlusMinus
      -- 1 0
      -- 0 0
      nonbranchingRepresentation InternalSpinPlusMinus `actOnKet` BitString 0b0 `shouldBe` (1, BitString 0b0)
      nonbranchingRepresentation InternalSpinPlusMinus `actOnKet` BitString 0b1 `shouldBe` (0, BitString 0b1)
      BitString 0b0 `actOnBra` nonbranchingRepresentation InternalSpinPlusMinus `shouldBe` (1, BitString 0b0)
      BitString 0b1 `actOnBra` nonbranchingRepresentation InternalSpinPlusMinus `shouldBe` (0, BitString 0b1)

      (nonbranchingRepresentation SpinZ <> nonbranchingRepresentation SpinPlus)
        `shouldBe` nonbranchingRepresentation SpinPlus
