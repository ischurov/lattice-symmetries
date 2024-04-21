-- |
-- Module      : LatticeSymmetries.Dense
-- Description : Dense matrices
-- Copyright   : (c) Tom Westerhout, 2022
-- Stability   : experimental
module LatticeSymmetries.Dense
  ( DenseMatrix (..)
  , dmShape
  , denseMatrixFromList
  , denseMatrixToList
  , unsafeIndexDenseMatrix
  , indexDenseMatrix
  , generateDenseMatrix
  )
where

import Data.Aeson (ToJSON (toJSON))
import Data.Vector.Generic qualified as G
import GHC.Exts qualified as GHC (IsList (..))

-- | A dense matrix in row-major order (C layout).
data DenseMatrix v a = DenseMatrix
  { dmRows :: !Int
  -- ^ Number of rows
  , dmCols :: !Int
  -- ^ Number of columns
  , dmData :: !(v a)
  -- ^ Matrix elements in row-major order stored in a 'Data.Vector.Generic.Vector'
  }
  deriving stock (Show, Eq, Generic)
  deriving anyclass (NFData)

instance (G.Vector v a, ToJSON a) => ToJSON (DenseMatrix v a) where
  toJSON m = toJSON (denseMatrixToList m)

-- | Get matrix shape
dmShape :: DenseMatrix v a -> (Int, Int)
dmShape m = (dmRows m, dmCols m)

-- | Element-wise operations
-- instance (G.Vector v a, Num a) => Num (DenseMatrix v a) where
--   (+) a b = DenseMatrix (dmRows a) (dmCols a) $ G.zipWith (+) (dmData a) (dmData b)
--   (-) a b = DenseMatrix (dmRows a) (dmCols a) $ G.zipWith (-) (dmData a) (dmData b)
--   (*) a b = DenseMatrix (dmRows a) (dmCols a) $ G.zipWith (*) (dmData a) (dmData b)
--   abs a = DenseMatrix (dmRows a) (dmCols a) $ G.map abs (dmData a)
--   signum a = DenseMatrix (dmRows a) (dmCols a) $ G.map signum (dmData a)
--   fromInteger _ = error "Num instance of DenseMatrix does not implement fromInteger"
denseMatrixFromList :: (HasCallStack, G.Vector v a) => [[a]] -> DenseMatrix v a
denseMatrixFromList rs
  | G.length elements == nRows * nCols = DenseMatrix nRows nCols elements
  | otherwise = error "nested list has irregular shape"
  where
    !nRows = length rs
    !nCols = case rs of
      [] -> 0
      (r : _) -> length r
    elements = G.fromListN (nRows * nCols) $ mconcat rs

denseMatrixToList :: G.Vector v a => DenseMatrix v a -> [[a]]
denseMatrixToList (DenseMatrix nRows nCols v) = go 0 (G.toList v)
  where
    go !i elements
      | i < nRows = let (row, rest) = splitAt nCols elements in row : go (i + 1) rest
      | otherwise = []

instance G.Vector v a => GHC.IsList (DenseMatrix v a) where
  type Item (DenseMatrix v a) = [a]
  fromList = denseMatrixFromList
  toList = denseMatrixToList

-- countOffDiagNonZero :: (G.Vector v a, Eq a, Num a) => DenseMatrix v a -> Int
-- countOffDiagNonZero m@(DenseMatrix nRows nCols _) = go1 0 0
--   where
--     go2 !i !j !acc
--       | i == j = go2 i (j + 1) acc
--       | j < nCols =
--         if indexDenseMatrix m (i, j) /= 0
--           then go2 i (j + 1) (acc + 1)
--           else go2 i (j + 1) acc
--       | otherwise = acc
--     go1 !i !acc
--       | i < nRows = let acc' = go2 i 0 acc in go1 (i + 1) acc'
--       | otherwise = acc
unsafeIndexDenseMatrix :: G.Vector v a => DenseMatrix v a -> (Int, Int) -> a
unsafeIndexDenseMatrix (DenseMatrix _ nCols v) (!i, !j) = G.unsafeIndex v (nCols * i + j)

indexDenseMatrix :: (HasCallStack, G.Vector v a) => DenseMatrix v a -> (Int, Int) -> a
indexDenseMatrix m@(DenseMatrix nRows nCols _) (i, j)
  | i < nRows && j < nCols = unsafeIndexDenseMatrix m (i, j)
  | otherwise = error $ "invalid index " <> show (i, j) <> " for a matrix of shape " <> show (nRows, nCols)

generateDenseMatrix :: G.Vector v a => Int -> Int -> (Int -> Int -> a) -> DenseMatrix v a
generateDenseMatrix nRows nCols f =
  DenseMatrix nRows nCols $
    G.generate (nRows * nCols) $
      \k -> let (!i, !j) = k `divMod` nCols in f i j

-- extractDiagonal :: (HasCallStack, G.Vector v a, G.Vector v Int) => DenseMatrix v a -> v a
-- extractDiagonal m@(DenseMatrix nRows nCols _)
--   | nRows == nCols = G.map (\i -> indexDenseMatrix m (i, i)) (G.enumFromN 0 nRows)
--   | otherwise = error "cannot extract the diagonal of a non-square matrix"

-- denseDot :: (G.Vector v a, Num a) => DenseMatrix v a -> DenseMatrix v a -> a
-- denseDot a b = let (DenseMatrix _ _ c) = a * b in G.sum c

-- denseMatMul :: forall a v. (G.Vector v a, Num a) => DenseMatrix v a -> DenseMatrix v a -> DenseMatrix v a
-- denseMatMul a b = runST $ do
--   let !nRows = dmRows a
--       !nCols = dmCols b
--   cBuffer <- GM.new (nRows * nCols)
--   loopM 0 (< nRows) (+ 1) $ \i ->
--     loopM 0 (< nCols) (+ 1) $ \j -> do
--       !cij <- iFoldM 0 (< dmCols a) (+ 1) (0 :: a) $ \ !acc k ->
--         let !aik = indexDenseMatrix a (i, k)
--             !bkj = indexDenseMatrix b (k, j)
--          in pure (acc + aik * bkj)
--       GM.write cBuffer (i * nCols + j) cij
--   DenseMatrix nRows nCols <$> G.unsafeFreeze cBuffer

-- denseEye :: (G.Vector v a, Num a) => Int -> DenseMatrix v a
-- denseEye n = runST $ do
--   cBuffer <- G.unsafeThaw $ G.replicate (n * n) 0
--   loopM 0 (< n) (+ 1) $ \i ->
--     GM.write cBuffer (i * n + i) 1
--   c <- G.freeze cBuffer
--   pure $ DenseMatrix n n c

-- denseIsDiagonal :: (G.Vector v a, Eq a, Num a) => DenseMatrix v a -> Bool
-- denseIsDiagonal m@(DenseMatrix nRows nCols _) = go1 0
--   where
--     go1 !i
--       | i < nRows = go2 i 0 && go1 (i + 1)
--       | otherwise = True
--     go2 !i !j
--       | i == j = go2 i (j + 1)
--       | j < nCols = indexDenseMatrix m (i, j) == 0 && go2 i (j + 1)
--       | otherwise = True
