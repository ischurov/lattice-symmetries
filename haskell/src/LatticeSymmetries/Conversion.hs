{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE PatternSynonyms #-}

module LatticeSymmetries.Conversion
  ( extractInteractions
  , spinsToFermions
  , convertedToInteractions
  , prepareHPhi
  , prepareVMC
  , Interactions (..)
  )
where

import Control.Exception (assert)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromJust)
import Data.Text qualified as Text
import Data.Text.IO qualified as Text
import Data.Vector.Generic (foldl1')
import Data.Vector.Generic qualified as G
import LatticeSymmetries.Algebra
import LatticeSymmetries.Basis
import LatticeSymmetries.ComplexRational
import LatticeSymmetries.Expr
import LatticeSymmetries.Generator
import LatticeSymmetries.Operator
import LatticeSymmetries.Utils
import System.Directory
import Prelude hiding (Product, Sum)

pattern C :: Int -> SpinIndex -> Generator (SpinIndex, Int) FermionGeneratorType
pattern C i s = Generator (s, i) FermionCreate

pattern A :: Int -> SpinIndex -> Generator (SpinIndex, Int) FermionGeneratorType
pattern A i s = Generator (s, i) FermionAnnihilate

pattern N :: Int -> SpinIndex -> Generator (SpinIndex, Int) FermionGeneratorType
pattern N i s = Generator (s, i) FermionCount

class PrettyStdFace a where
  prettyStdFace :: a -> Text

instance PrettyStdFace Text where
  prettyStdFace = id

instance PrettyStdFace Int where
  prettyStdFace = show

instance PrettyStdFace Char where
  prettyStdFace = Text.singleton

instance PrettyStdFace Double where
  prettyStdFace = show

instance PrettyStdFace Rational where
  prettyStdFace = prettyStdFace . realToFrac @_ @Double

instance PrettyStdFace ComplexRational where
  prettyStdFace z = prettyStdFace (realPart z, imagPart z)

instance PrettyStdFace SpinIndex where
  prettyStdFace = prettyStdFace . fromEnum

instance (PrettyStdFace a, PrettyStdFace b) => PrettyStdFace (a, b) where
  prettyStdFace (a, b) = Text.unwords [prettyStdFace a, prettyStdFace b]

instance (PrettyStdFace a, PrettyStdFace b, PrettyStdFace c) => PrettyStdFace (a, b, c) where
  prettyStdFace (a, b, c) = Text.unwords [prettyStdFace (a, b), prettyStdFace c]

instance
  (PrettyStdFace a, PrettyStdFace b, PrettyStdFace c, PrettyStdFace d)
  => PrettyStdFace (a, b, c, d)
  where
  prettyStdFace (a, b, c, d) = Text.unwords [prettyStdFace (a, b, c), prettyStdFace d]

instance
  (PrettyStdFace a, PrettyStdFace b, PrettyStdFace c, PrettyStdFace d, PrettyStdFace e)
  => PrettyStdFace (a, b, c, d, e)
  where
  prettyStdFace (a, b, c, d, e) = Text.unwords [prettyStdFace (a, b, c, d), prettyStdFace e]

data TransferIntegral = TransferIntegral !Int !SpinIndex !Int !SpinIndex !ComplexRational

instance CanScale ComplexRational TransferIntegral where
  scale z (TransferIntegral i1 s1 i2 s2 c) = TransferIntegral i1 s1 i2 s2 (z * c)

instance PrettyStdFace TransferIntegral where
  prettyStdFace (TransferIntegral i1 s1 i2 s2 c) = prettyStdFace (i1, s1, i2, s2, -c)

toTransferIntegral
  :: (i ~ IndexType 'SpinfulFermionTy, g ~ GeneratorType 'SpinfulFermionTy)
  => Product (Generator i g)
  -> Maybe TransferIntegral
toTransferIntegral p = case toList p of
  -- NOTE: We guarantee that after simplifyExpr, there aren't products where with multiple
  -- operators have the same index
  [C i1 s1, A i2 s2] -> Just $ TransferIntegral i1 s1 i2 s2 1
  [g1@(A _ _), g2@(C _ _)] -> minus $ toTransferIntegral [g2, g1]
  _ -> Nothing
  where
    minus = fmap (scale (-1 :: ComplexRational))

data TwoBodyInteraction
  = TwoBodyInteraction !Int !SpinIndex !Int !SpinIndex !Int !SpinIndex !Int !SpinIndex !ComplexRational
  deriving stock (Show)

instance CanScale ComplexRational TwoBodyInteraction where
  scale z (TwoBodyInteraction i1 s1 i2 s2 i3 s3 i4 s4 c) =
    TwoBodyInteraction i1 s1 i2 s2 i3 s3 i4 s4 (z * c)

instance PrettyStdFace TwoBodyInteraction where
  prettyStdFace (TwoBodyInteraction i1 s1 i2 s2 i3 s3 i4 s4 c) =
    prettyStdFace ((i1, s1), (i2, s2), (i3, s3), (i4, s4), c)

toTwoBodyInteraction
  :: (i ~ IndexType 'SpinfulFermionTy, g ~ GeneratorType 'SpinfulFermionTy)
  => Product (Generator i g)
  -> Maybe TwoBodyInteraction
toTwoBodyInteraction p = case toList p of
  [C i1 s1, A i2 s2, C i3 s3, A i4 s4] ->
    if i1 /= i2 && i2 == i3
      then Just $ TwoBodyInteraction i3 s3 i2 s2 i1 s1 i4 s4 (-1)
      else Just $ TwoBodyInteraction i1 s1 i2 s2 i3 s3 i4 s4 1
  [g1@(C _ _), g2@(C _ _), g3@(A _ _), g4@(A _ _)] -> minus $ toTwoBodyInteraction [g1, g3, g2, g4]
  [g1@(C _ _), g2@(A _ _), g3@(A _ _), g4@(C _ _)] -> minus $ toTwoBodyInteraction [g1, g2, g4, g3]
  [g1@(A _ _), g2@(C _ _), g3@(C _ _), g4@(A _ _)] -> minus $ toTwoBodyInteraction [g2, g1, g3, g4]
  [g1@(A _ _), g2@(C _ _), g3@(A _ _), g4@(C _ _)] -> toTwoBodyInteraction [g2, g1, g4, g3]
  [g1@(A _ _), g2@(A _ _), g3@(C _ _), g4@(C _ _)] -> minus $ toTwoBodyInteraction [g4, g2, g3, g1]
  _ -> Nothing
  where
    minus = fmap (scale (-1 :: ComplexRational))

data CoulombIntra = CoulombIntra !Int !ComplexRational

instance CanScale ComplexRational CoulombIntra where
  scale z (CoulombIntra i c) = CoulombIntra i (z * c)

instance PrettyStdFace CoulombIntra where
  prettyStdFace (CoulombIntra i c) = assert (imagPart c == 0) $ prettyStdFace (i, realPart c)

toCoulombIntra
  :: (i ~ IndexType 'SpinfulFermionTy, g ~ GeneratorType 'SpinfulFermionTy)
  => Product (Generator i g)
  -> Maybe CoulombIntra
toCoulombIntra p = case toList p of
  [N i1 _, N i2 _] | i1 == i2 -> Just $ CoulombIntra i1 1
  _ -> Nothing

attemptConversion :: (a -> Maybe b) -> [a] -> ([b], [a])
attemptConversion f xs = partitionEithers (f' <$> xs)
  where
    f' x = maybe (Right x) Left (f x)

generateContents :: PrettyStdFace a => Text -> Int -> Text -> [a] -> Text
generateContents name count header selected =
  Text.unlines $
    [ horizontalLine
    , name <> " " <> show count
    , horizontalLine
    , headerLine
    , horizontalLine
    ]
      <> fmap prettyStdFace selected
  where
    headerLine = "========" <> header <> "========"
    horizontalLine = Text.replicate (Text.length headerLine) "="

extractViaConversion
  :: ( t ~ 'SpinfulFermionTy
     , i ~ IndexType t
     , g ~ GeneratorType t
     , PrettyStdFace a
     , CanScale ComplexRational a
     )
  => (Product (Generator i g) -> Maybe a)
  -> Expr t
  -> ([a], Expr t)
extractViaConversion convert (Expr (Sum terms)) = (selected, Expr (fromList others))
  where
    (selected, others) = attemptConversion (\(Scaled c p) -> scale c <$> convert p) (toList terms)

extractViaSubtraction
  :: ( g ~ Generator (IndexType t) (GeneratorType t)
     , IsBasis t
     , Ord i
     )
  => (Scaled (Product g) -> Maybe (i, ℂ))
  -> (i -> ℂ -> a)
  -> (a -> [Scaled (Product g)])
  -> Expr t
  -> ([a], Expr t)
extractViaSubtraction isRelevant toInteraction toTerms expr@(Expr (Sum terms)) = (interactions, others)
  where
    others = expr - Expr (fromList (concatMap toTerms interactions))
    interactions = uncurry toInteraction <$> Map.toList coeffsMap
    coeffsMap = G.foldl' combineMap Map.empty relevantTerms
    relevantTerms = G.map fromJust . G.filter isJust . G.map isRelevant $ terms
    combineMap coeffs (i, c) = Map.insertWith combineCoeffs i c coeffs
    combineCoeffs new old = if magnitudeSquared new > magnitudeSquared old then new else old

data CoulombInter = CoulombInter !(Int, Int) !ℂ

instance PrettyStdFace CoulombInter where
  prettyStdFace (CoulombInter i c) = assert (imagPart c == 0) $ prettyStdFace (i, realPart c)

extractCoulombInter :: Expr 'SpinfulFermionTy -> ([CoulombInter], Expr 'SpinfulFermionTy)
extractCoulombInter = extractViaSubtraction isRelevant CoulombInter toTerms
  where
    isRelevant (Scaled c (Product p)) = case toList p of
      [N i1 s1, N i2 s2] | i1 /= i2 && s1 /= s2 -> (,c) <$> if i1 < i2 then Just (i1, i2) else Just (i2, i1)
      _ -> Nothing
    toTerms (CoulombInter (i1, i2) c) =
      [ Scaled c [N i1 SpinUp, N i2 SpinUp]
      , Scaled c [N i1 SpinUp, N i2 SpinDown]
      , Scaled c [N i1 SpinDown, N i2 SpinUp]
      , Scaled c [N i1 SpinDown, N i2 SpinDown]
      ]

data Hund = Hund !(Int, Int) !ℂ

instance PrettyStdFace Hund where
  prettyStdFace (Hund i c) = assert (imagPart c == 0) $ prettyStdFace (i, -realPart c)

extractHund :: Expr 'SpinfulFermionTy -> ([Hund], Expr 'SpinfulFermionTy)
extractHund = extractViaSubtraction isRelevant Hund toTerms
  where
    isRelevant (Scaled c (Product p)) = case toList p of
      [N i1 s1, N i2 s2] | i1 /= i2 && s1 == s2 -> (,c) <$> if i1 < i2 then Just (i1, i2) else Just (i2, i1)
      _ -> Nothing
    toTerms (Hund (i1, i2) c) =
      [ Scaled c [N i1 SpinUp, N i2 SpinUp]
      , Scaled c [N i1 SpinDown, N i2 SpinDown]
      ]

data Exchange = Exchange !(Int, Int) !ℂ
  deriving stock (Show)

instance PrettyStdFace Exchange where
  prettyStdFace (Exchange i c) = assert (imagPart c == 0) $ prettyStdFace (i, realPart c)

extractExchange :: Expr 'SpinfulFermionTy -> ([Exchange], Expr 'SpinfulFermionTy)
extractExchange = extractViaSubtraction isRelevant Exchange toTerms
  where
    isRelevant (Scaled c (Product p)) = case toList p of
      [C i1 SpinUp, A i2 SpinUp, A i1' SpinDown, C i2' SpinDown]
        | i1 /= i2 && i1 == i1' && i2 == i2' -> Just ((i1, i2), -c)
      [A i1 SpinUp, C i2 SpinUp, C i1' SpinDown, A i2' SpinDown]
        | i1 /= i2 && i1 == i1' && i2 == i2' -> Just ((i1, i2), -c)
      _ -> Nothing
    toTerms (Exchange (i1, i2) c) =
      [ Scaled c [C i1 SpinUp, A i2 SpinUp, C i2 SpinDown, A i1 SpinDown]
      , Scaled c [C i1 SpinDown, A i2 SpinDown, C i2 SpinUp, A i1 SpinUp]
      ]

generateLocSpin :: Basis t -> Text
generateLocSpin basis = case basis of
  SpinBasis n _ _ _ -> contents n '1'
  SpinfulFermionBasis n _ -> contents n '0'
  SpinlessFermionBasis n _ -> contents n '0'
  where
    contents n k = generateContents "NlocalSpin" (count n k) "i_0LocSpn_1IteElc" [(i, k) | i <- [0 .. n - 1]]
    count n k = if k == '0' then 0 else n

generateCalcModHPhi :: Basis t -> Text
generateCalcModHPhi basis =
  Text.unlines
    [ "CalcType 0"
    , "CalcModel " <> calcModel
    , "CalcEigenVec 1"
    , "OutputEigenVec 1"
    ]
  where
    calcModel = case basis of
      SpinBasis _ Nothing _ _ -> "4"
      SpinBasis {} -> "1"
      _ -> "0"

generateModParaHPhi :: Basis t -> Text
generateModParaHPhi basis =
  Text.unlines $
    [ "--------------------"
    , "Model_Parameters   0"
    , "--------------------"
    , "VMC_Cal_Parameters"
    , "--------------------"
    , "CDataFileHead  zvo"
    , "CParaFileHead  zqp"
    , "--------------------"
    ]
      <> systemInfo
      <> ["exct 1", "Lanczos_max 100", "LanczosEps 12"]
  where
    systemInfo = case basis of
      SpinBasis n occ _ _ ->
        fmap (prettyStdFace @(Text, Int)) $
          [("Nsite", n)] <> maybe [] (\h -> [("2Sz ", 2 * h - n)]) occ
      SpinlessFermionBasis n occ ->
        fmap (prettyStdFace @(Text, Int)) $
          [("Nsite ", n)] <> maybe [] (\k -> [("Ncond", k), ("2Sz", k)]) occ
      SpinfulFermionBasis n occ ->
        let ncond
              | SpinfulNoOccupation <- occ = []
              | SpinfulTotalParticles k <- occ = ["Ncond " <> show k]
              | SpinfulPerSector k1 k2 <- occ = ["Ncond " <> show (k1 + k2)]
            twoSz
              | SpinfulPerSector k1 k2 <- occ = ["2Sz " <> show (k1 - k2)]
              | otherwise = []
         in ["Nsite " <> show n] <> ncond <> twoSz

generateModParaVMC :: Basis t -> Text
generateModParaVMC basis =
  Text.unlines $
    [ "--------------------"
    , "Model_Parameters   0"
    , "--------------------"
    , "VMC_Cal_Parameters"
    , "--------------------"
    , "CDataFileHead   zvo"
    , "CParaFileHead   zqp"
    , "--------------------"
    , "NVMCCalMode     0"
    , "NLanczosMode    0"
    , "--------------------"
    , "NDataIdxStart   0"
    , "NDataQtySmp     1"
    , "--------------------"
    , -- NOTE: when symmetries are not used, we have to set NMPTrans=1
      "NMPTrans 1"
    ]
      <> nsite
      <> ncond
      <> twoSz
      <> exupdate
  where
    nsite = ["Nsite " <> show (getNumberSites basis)]
    ncond = maybe [] (\(k :: Int) -> ["Ncond " <> show k]) $
      case basis of
        SpinlessFermionBasis _ occ -> occ
        SpinfulFermionBasis _ (SpinfulTotalParticles k) -> Just k
        SpinfulFermionBasis _ (SpinfulPerSector k1 k2) -> Just (k1 + k2)
        _ -> Nothing
    twoSz = maybe [] (\(k :: Int) -> ["2Sz " <> show k]) $
      case basis of
        SpinBasis n (Just h) _ _ -> Just (2 * h - n)
        SpinfulFermionBasis _ (SpinfulPerSector k1 k2) -> Just (k1 - k2)
        _ -> Nothing
    exupdate = (\k -> ["NExUpdatePath " <> k]) $ case basis of
      SpinBasis {} -> "2"
      _ -> "1"

generateTransSymVMC :: Basis t -> Text
generateTransSymVMC basis =
  Text.unlines $
    [ "============================================="
    , "NQPTrans 1"
    , "============================================="
    , "======== TrIdx_TrWeight_and_TrIdx_i_xi ======"
    , "============================================="
    , "0 1.0"
    ]
      <> [Text.unwords ["0", show i, show i] | i <- [0 .. n - 1]]
  where
    n = getNumberSites basis

-- generateGutzwillerIdx :: Basis t -> Text
-- generateGutzwillerIdx basis =
--   Text.unlines $
--     [ "======================"
--     , "NGutzwillerIdx " <> show n
--     , "ComplexType 0"
--     , "======================"
--     , "======================"
--     ]
--       <> [show i <> " " <> show i | i <- [0 .. n - 1]]
--       <> [show i <> " 1" | i <- [0 .. n - 1]]
--   where
--     n = getNumberSites basis

generateOrbitalVMC :: Basis t -> Text
generateOrbitalVMC basis =
  Text.unlines $
    [ "======================"
    , "NOrbitalIdx " <> show (length indicesGeneral)
    , "ComplexType 1"
    , "======================"
    , "======================"
    ]
      <> indicesGeneral
      <> parameters
  where
    n = getNumberSites basis
    indicesGeneral =
      zipWith
        (\(i1, s1, i2, s2) k -> Text.unwords $ show <$> [i1, s1, i2, s2, k])
        [ (i1, s1, i2, s2)
        | s1 <- [0 .. 1]
        , s2 <- [0 .. 1]
        , i1 <- [0 .. n - 1]
        , i2 <- [0 .. n - 1]
        , i1 + s1 * n < i2 + s2 * n
        ]
        [0 ..]
    parameters =
      [show k <> " 1" | k <- [0 .. length indicesGeneral - 1]]

spinsToFermions :: Expr 'SpinTy -> Expr 'SpinfulFermionTy
spinsToFermions = simplifyExpr . sumToFermions . unExpr
  where
    sumToFermions (Sum xs) =
      foldl1' (+) $ (\(Scaled c p) -> scale c (productToFermions p)) <$> xs
    productToFermions (Product xs) = foldl1' (*) $ generatorToFermions <$> xs
    generatorToFermions (Generator i g) = case g of
      SpinPlus ->
        Expr [Scaled 1 [Generator (SpinUp, i) FermionCreate, Generator (SpinDown, i) FermionAnnihilate]]
      SpinMinus ->
        Expr [Scaled 1 [Generator (SpinDown, i) FermionCreate, Generator (SpinUp, i) FermionAnnihilate]]
      SpinZ ->
        Expr
          [ Scaled 1 [Generator (SpinUp, i) FermionCount]
          , Scaled (-1) [Generator (SpinDown, i) FermionCount]
          ]
      SpinIdentity -> Expr [Scaled 1 [Generator (SpinUp, i) FermionIdentity]]

data Interactions = Interactions
  { trans :: [TransferIntegral]
  , coulombIntra :: [CoulombIntra]
  , coulombInter :: [CoulombInter]
  , hund :: [Hund]
  , exchange :: [Exchange]
  , interAll :: [TwoBodyInteraction]
  }

extractInteractions :: Expr 'SpinfulFermionTy -> (Interactions, Expr 'SpinfulFermionTy)
extractInteractions expr0 = (hphi, expr6)
  where
    hphi =
      Interactions
        { trans = trans
        , coulombIntra = coulombIntra
        , coulombInter = coulombInter
        , hund = hund
        , exchange = exchange
        , interAll = interAll
        }
    (trans, expr1) = extractViaConversion toTransferIntegral expr0
    (coulombIntra, expr2) = extractViaConversion toCoulombIntra expr1
    (coulombInter, expr3) = extractCoulombInter expr2
    (hund, expr4) = extractHund expr3
    (exchange, expr5) = extractExchange expr4
    -- expr5 = expr4
    -- exchange = []
    (interAll, expr6) = extractViaConversion toTwoBodyInteraction expr5

writeCommon :: Basis t -> Interactions -> FilePath -> IO [Text]
writeCommon basis int folder = do
  let writeUnlessNull :: PrettyStdFace a => FilePath -> Text -> Text -> [a] -> IO ()
      writeUnlessNull suffix name header terms =
        unless (null terms) $
          Text.writeFile (folder <> "/" <> suffix) $
            generateContents name (length terms) header terms
  Text.writeFile (folder <> "/LocSpin.def") $ generateLocSpin basis
  writeUnlessNull "Trans.def" "NTransfer" "i_j_s_tijs" int.trans
  writeUnlessNull "CoulombIntra.def" "NCoulombIntra" "i_0LocSpn_1IteElc" int.coulombIntra
  writeUnlessNull "CoulombInter.def" "NCoulombInter" "CoulombInter" int.coulombInter
  writeUnlessNull "Hund.def" "NHund" "Hund" int.hund
  writeUnlessNull "Exchange.def" "NExchange" "Exchange" int.exchange
  writeUnlessNull "InterAll.def" "NInterAll" "zInterAll" int.interAll
  -- unless (null int.trans) $
  --   Text.writeFile (folder <> "/Trans.def") $
  --     generateContents "NTransfer" (length int.trans) "i_j_s_tijs" int.trans
  -- unless (null int.coulombIntra) $
  --   Text.writeFile (folder <> "/CoulombIntra.def") $
  --     generateContents "NCoulombIntra" (length int.coulombIntra) "i_0LocSpn_1IteElc" int.coulombIntra
  -- unless (null int.coulombInter) $
  --   Text.writeFile (folder <> "/CoulombInter.def") $
  --     generateContents "NCoulombInter" (length int.coulombInter) "CoulombInter" int.coulombInter
  -- unless (null int.hund) $
  --   Text.writeFile (folder <> "/Hund.def") $
  --     generateContents "NHund" (length int.hund) "Hund" int.hund
  -- unless (null int.exchange) $
  --   Text.writeFile (folder <> "/Hund.def") $
  --     generateContents "NHund" (length int.hund) "Hund" int.hund
  -- unless (null int.interAll) $
  --   Text.writeFile (folder <> "/InterAll.def") $
  --     generateContents "NInterAll" (length int.interAll) "zInterAll" int.interAll
  pure $
    concat @[]
      [ ["LocSpin LocSpin.def"]
      , ["Trans Trans.def" | not (null int.trans)]
      , ["CoulombIntra CoulombIntra.def" | not (null int.coulombIntra)]
      , ["CoulombInter CoulombInter.def" | not (null int.coulombInter)]
      , ["Hund Hund.def" | not (null int.hund)]
      , ["Exchange Exchange.def" | not (null int.exchange)]
      , ["InterAll InterAll.def" | not (null int.interAll)]
      ]

convertedToInteractions :: forall a. HasCallStack => SomeOperator -> (forall t. IsBasis t => Basis t -> Interactions -> a) -> a
convertedToInteractions op f = case op of
  (SomeOperator SpinTag (Operator basis spinExpr)) -> run basis $ extractInteractions (spinsToFermions spinExpr)
  (SomeOperator SpinfulFermionTag (Operator basis expr)) -> run basis $ extractInteractions expr
  (SomeOperator SpinlessFermionTag _) -> error "spinless fermions are not yet supported"
  where
    run :: forall t1 t2. (IsBasis t1, IsBasis t2) => Basis t1 -> (Interactions, Expr t2) -> a
    run basis (int, others) =
      if others == Expr []
        then f basis int
        else error $ "some interaction terms could not be handled: " <> toPrettyText others

prepareHPhi :: Text -> Basis t -> Interactions -> IO ()
prepareHPhi (Text.unpack -> folder) basis int = do
  createDirectoryIfMissing True folder
  Text.writeFile (folder <> "/CalcMod.def") $ generateCalcModHPhi basis
  Text.writeFile (folder <> "/ModPara.def") $ generateModParaHPhi basis
  common <- writeCommon basis int folder
  Text.writeFile (folder <> "/namelist.def") $
    Text.unlines $
      ["CalcMod CalcMod.def", "ModPara ModPara.def"] <> common

prepareVMC :: Text -> Basis t -> Interactions -> IO ()
prepareVMC (Text.unpack -> folder) basis int = do
  createDirectoryIfMissing True folder
  Text.writeFile (folder <> "/ModPara.def") $ generateModParaVMC basis
  Text.writeFile (folder <> "/Orbital.def") $ generateOrbitalVMC basis
  Text.writeFile (folder <> "/TransSym.def") $ generateTransSymVMC basis
  common <- writeCommon basis int folder
  Text.writeFile (folder <> "/namelist.def") $
    Text.unlines $
      [ "ModPara ModPara.def"
      , "OrbitalGeneral Orbital.def"
      , "TransSym TransSym.def"
      ]
        <> common
