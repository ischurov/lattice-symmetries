{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module LatticeSymmetries.Lowering
  ( createIsRepresentativeKernel_v2
  , destroyIsRepresentativeKernel_v2
  , createStateInfoKernel_v2
  , destroyStateInfoKernel_v2
  , createFixedHammingStateToIndexKernel
  , destroyFixedHammingStateToIndexKernel
  , invokeIsRepresentativeKernel
  , invokeStateInfoKernel
  , invokeFixedHammingStateToIndexKernel
  , freeFunPtrClosure
  , compileGroupRepresentation
  , fixedHammingIndexToState
  , fixedHammingStateToIndex
  , toFun_fixed_hamming_state_to_index_kernel
  , ls_hs_fixed_hamming_state_to_index
  , ls_hs_fixed_hamming_index_to_state
  , binomial
  )
where

import Control.Monad.ST (runST)
import Data.Bits (bit, countTrailingZeros, (.&.), (.|.))
import Data.Complex (imagPart, realPart)
import Data.Maybe qualified
import Data.Vector qualified as B
import Data.Vector.Generic qualified as G
import Data.Vector.Generic.Mutable qualified as GM
import Data.Vector.Storable qualified as S
import Foreign (FunPtr, Storable, castPtr, nullFunPtr)
import Foreign.C (CInt (..))
import Foreign.ForeignPtr.Unsafe (unsafeForeignPtrToPtr)
import Language.C.Inline.Unsafe qualified as CU
import Language.Halide hiding (dim)
import LatticeSymmetries.Automorphisms
import LatticeSymmetries.Benes
import LatticeSymmetries.Context
import LatticeSymmetries.Dense
import LatticeSymmetries.Group
import LatticeSymmetries.Permutation
import LatticeSymmetries.Utils (loopM)
import Prelude hiding (group, permutations, state, (/=), (<), (<=), (==), (>), (>=))

importLS

computeBinomials :: Int -> DenseMatrix S.Vector Word64
computeBinomials dim = transposeDenseMatrix $ runST $ do
  coeff <- GM.replicate (dim * dim) 0
  GM.write coeff 0 1
  loopM 1 (< dim) (+ 1) $ \n -> do
    GM.write coeff (n * dim) 1
    loopM 1 (<= n) (+ 1) $ \k ->
      GM.write coeff (n * dim + k)
        =<< (+)
          <$> GM.read coeff ((n - 1) * dim + k - 1)
          <*> GM.read coeff ((n - 1) * dim + k)
  DenseMatrix dim dim <$> G.unsafeFreeze coeff

binomialsCache :: DenseMatrix S.Vector Word64
binomialsCache = computeBinomials 65
{-# NOINLINE binomialsCache #-}

binomial :: Int -> Int -> Maybe Int
binomial n k
  | n <= 0 || k > n = Just 0
  | otherwise = toIntegralSized $ indexDenseMatrix binomialsCache (k, n)

-- binomial :: Int -> Int -> Maybe Int
-- binomial n k
--   | n <= 0 || k > n = Just 0
--   | otherwise = toIntegralSized $ factorial n `div` factorial (n - k) `div` factorial k
--   where
--     factorial :: Int -> Integer
--     factorial x = product ([1 .. fromIntegral x] :: [Integer])

fixedHammingStateToIndex :: Word64 -> Int
fixedHammingStateToIndex = go 0 1
  where
    go !i !k !α
      | α /= 0 =
          let c = countTrailingZeros α
              α' = α .&. (α - 1)
              i' = i + Data.Maybe.fromJust (binomial c k)
           in go i' (k + 1) α'
      | otherwise = i

fixedHammingIndexToState :: Int -> Int -> Word64
fixedHammingIndexToState hammingWeight = go hammingWeight 0
  where
    go !i !state !index
      | i <= 0 = state
      | otherwise = go (i - 1) state' index'
      where
        (c, contribution) = inner index i (i - 1) 0
        -- (Data.Maybe.fromJust (binomial c i))
        state' = state .|. bit c
        index' = index - contribution
    inner !index !i !c !contribution
      | c >= numberBits = (c, contribution)
      | otherwise =
          if contribution' > index
            then (c, contribution)
            else inner index i c' contribution'
      where
        numberBits = 64
        c' = c + 1
        contribution' = Data.Maybe.fromJust (binomial c' i)

-- vectorToManagedHalideBuffer :: (Storable a, IsHalideType a) => S.Vector a -> IO (Ptr (ManagedHalideBuffer 1 a))
-- vectorToManagedHalideBuffer v = managedFromCpuPtrShapeStrides v cpuDataPtr [S.length v] [1]
--   where
--     cpuDataPtr = unsafeForeignPtrToPtr . fst . S.unsafeToForeignPtr0 $ v

transposeDenseMatrix :: G.Vector v a => DenseMatrix v a -> DenseMatrix v a
transposeDenseMatrix m
  | m.dmRows /= m.dmCols = error "cannot transpose a rectangular matrix"
  | otherwise = DenseMatrix n n $ G.generate (m.dmRows * m.dmCols) f
  where
    !n = m.dmRows
    f !k = let (i, j) = k `divMod` n in indexDenseMatrix m (j, i)

-- matrixToManagedHalideBuffer :: (Storable a, IsHalideType a) => DenseMatrix S.Vector a -> IO (Ptr (ManagedHalideBuffer 2 a))
-- matrixToManagedHalideBuffer m = managedFromCpuPtrShapeStrides m cpuDataPtr [m.dmRows, m.dmCols] [m.dmCols, 1]
--   where
--     cpuDataPtr = unsafeForeignPtrToPtr . fst . S.unsafeToForeignPtr0 $ m.dmData

instance (Storable a, IsHalideType a) => IsHalideBuffer (DenseMatrix S.Vector a) 2 a where
  withHalideBufferImpl m = bufferFromPtrShapeStrides cpuDataPtr [m.dmRows, m.dmCols] [m.dmCols, 1]
    where
      cpuDataPtr = unsafeForeignPtrToPtr . fst . S.unsafeToForeignPtr0 $ m.dmData

-- typedef void (*ls_hs_is_representative_kernel_type_v2)(halide_buffer_t const* basis_states, halide_buffer_t* norms);
foreign import ccall unsafe "dynamic"
  toFun_is_representative_kernel :: FunPtr RawIsRepresentativeKernel -> RawIsRepresentativeKernel

foreign import ccall unsafe "dynamic"
  toFun_state_info_kernel :: FunPtr RawStateInfoKernel -> RawStateInfoKernel

foreign import ccall unsafe "dynamic"
  toFun_fixed_hamming_state_to_index_kernel :: FunPtr RawStateToIndexKernel -> RawStateToIndexKernel

-- |
-- @
-- int ls_internal_is_representative_general_kernel(struct halide_buffer_t *_x_buffer, uint64_t _flip_mask, struct halide_buffer_t *_masks_buffer, struct halide_buffer_t *_eigvals_re_buffer, struct halide_buffer_t *_shifts_buffer, struct halide_buffer_t *_is_representative__3_buffer, struct halide_buffer_t *_norm__3_buffer);
-- @
-- foreign import ccall unsafe "ls_internal_is_representative_general_kernel"
--   ls_hs_internal_is_representative_kernel
--     :: Ptr RawHalideBuffer
--     -- ^ x
--     -> Word64
--     -- ^ flip_mask
--     -> Ptr (HalideBuffer 2 Word64)
--     -- ^ masks
--     -> Ptr (HalideBuffer 1 Double)
--     -- ^ eigvals_re
--     -> Ptr (HalideBuffer 1 Double)
--     -- ^ eigvals_im
--     -> Ptr (HalideBuffer 1 Word64)
--     -- ^ shifts
--     -> Ptr (HalideBuffer 1 Word8)
--     -- ^ is_representative
--     -> Ptr (HalideBuffer 1 Double)
--     -- ^ norm
--     -> IO ()
foreign import ccall unsafe "mk_is_representative_kernel"
  mk_is_representative_kernel
    :: Ptr (HalideBuffer 2 Word64)
    -- ^ masks
    -> Ptr (HalideBuffer 1 Double)
    -- ^ eigvals_re
    -> Ptr (HalideBuffer 1 Word64)
    -- ^ shifts
    -> CInt
    -- ^ spin_inversion
    -> IO (FunPtr RawIsRepresentativeKernel)

foreign import ccall unsafe "mk_state_info_kernel"
  mk_state_info_kernel
    :: Ptr (HalideBuffer 2 Word64)
    -- ^ masks
    -> Ptr (HalideBuffer 1 Word64)
    -- ^ shifts
    -> CInt
    -- ^ spin_inversion
    -> IO (FunPtr RawStateInfoKernel)

foreign import ccall unsafe "mk_fixed_hamming_state_to_index_kernel"
  mk_fixed_hamming_state_to_index_kernel
    :: CInt
    -> CInt
    -> Ptr (HalideBuffer 2 Word64)
    -> IO (FunPtr RawStateToIndexKernel)

-- getBufferShape :: Ptr RawHalideBuffer -> IO [Int]
-- getBufferShape p = do
--   buf <- peek p
--   forM [0 .. fromIntegral buf.halideBufferDimensions - 1] $
--     fmap (fromIntegral . (.halideDimensionExtent))
--       . peekElemOff buf.halideBufferDim

data Symmetries = Symmetries
  { symmGroup :: !PermutationGroup
  , symmNetwork :: !BatchedBenesNetwork
  , symmCharactersReal :: !(S.Vector Double)
  , symmCharactersImag :: !(S.Vector Double)
  , symmOriginal :: !(B.Vector Symmetry)
  }
  deriving stock (Show, Eq)

nullSymmetries :: Symmetries -> Bool
nullSymmetries = nullPermutationGroup . symmGroup

emptySymmetries :: Symmetries
emptySymmetries = Symmetries emptyPermutationGroup emptyBatchedBenesNetwork G.empty G.empty G.empty

compileGroupRepresentation :: HasCallStack => Representation Permutation -> Symmetries
compileGroupRepresentation (unRepresentation -> symmetries)
  | G.null symmetries = emptySymmetries
  | (G.head symmetries).size <= 1 = emptySymmetries
  | otherwise = Symmetries permGroup benesNetwork charactersReal charactersImag symmetries
  where
    permutations = (.element) <$> symmetries
    permGroup = mkPermutationGroup permutations
    benesNetwork = mkBatchedBenesNetwork $ G.map permutationToBenesNetwork permutations
    characters = G.convert $ (.character) <$> symmetries
    charactersReal = G.map realPart characters
    charactersImag = G.map imagPart characters

createIsRepresentativeKernel_v2 :: HasCallStack => Representation Permutation -> Maybe Int -> IO (FunPtr RawIsRepresentativeKernel)
createIsRepresentativeKernel_v2 _ (Just _) = error "not yet implemented"
createIsRepresentativeKernel_v2 group Nothing = do
  let !symms = compileGroupRepresentation group
  when (nullSymmetries symms) $ error "cannot compile for an empty or trivial group"
  withHalideBuffer @2 @Word64 symms.symmNetwork.bbnMasks $ \masksBuf ->
    withHalideBuffer @1 @Double symms.symmCharactersReal $ \eigvalsReBuf ->
      withHalideBuffer @1 @Word64 symms.symmNetwork.bbnShifts $ \shiftsBuf ->
        mk_is_representative_kernel
          masksBuf
          eigvalsReBuf
          shiftsBuf
          0

createStateInfoKernel_v2 :: HasCallStack => Representation Permutation -> Maybe Int -> IO (FunPtr RawStateInfoKernel)
createStateInfoKernel_v2 _ (Just _) = error "not yet implemented"
createStateInfoKernel_v2 group Nothing = do
  let !symms = compileGroupRepresentation group
  when (nullSymmetries symms) $ error "cannot compile for an empty or trivial group"
  withHalideBuffer @2 @Word64 symms.symmNetwork.bbnMasks $ \masksBuf ->
    withHalideBuffer @1 @Word64 symms.symmNetwork.bbnShifts $ \shiftsBuf ->
      mk_state_info_kernel
        masksBuf
        shiftsBuf
        0

freeFunPtrClosureIfNotNull :: FunPtr f -> IO ()
freeFunPtrClosureIfNotNull p
  | p /= nullFunPtr = freeFunPtrClosure p
  | otherwise = pure ()

destroyIsRepresentativeKernel_v2 :: FunPtr RawIsRepresentativeKernel -> IO ()
destroyIsRepresentativeKernel_v2 = freeFunPtrClosureIfNotNull

destroyStateInfoKernel_v2 :: FunPtr RawStateInfoKernel -> IO ()
destroyStateInfoKernel_v2 = freeFunPtrClosureIfNotNull

invokeIsRepresentativeKernel :: FunPtr RawIsRepresentativeKernel -> S.Vector Word64 -> IO (S.Vector Double)
invokeIsRepresentativeKernel funPtr basisStates =
  withHalideBuffer @1 @Word64 basisStates $ \basisStatesBuf ->
    allocaCpuBuffer [S.length basisStates] $ \normsBuf -> do
      toFun_is_representative_kernel funPtr (castPtr basisStatesBuf) (castPtr normsBuf)
      S.fromList <$> peekToList normsBuf

invokeStateInfoKernel :: FunPtr RawStateInfoKernel -> S.Vector Word64 -> IO (S.Vector Word64, S.Vector Int32)
invokeStateInfoKernel funPtr basisStates =
  withHalideBuffer @1 @Word64 basisStates $ \basisStatesBuf ->
    allocaCpuBuffer [S.length basisStates] $ \repsBuf ->
      allocaCpuBuffer [S.length basisStates] $ \indicesBuf -> do
        toFun_state_info_kernel funPtr (castPtr basisStatesBuf) (castPtr repsBuf) (castPtr indicesBuf)
        (,) <$> (S.fromList <$> peekToList repsBuf) <*> (S.fromList <$> peekToList indicesBuf)

createFixedHammingStateToIndexKernel :: HasCallStack => Int -> Int -> IO (FunPtr RawStateToIndexKernel)
createFixedHammingStateToIndexKernel numberSites hammingWeight = do
  -- let !binomials = binomialsCache -- (computeBinomials {-numberSites-} 65)
  withHalideBuffer @2 @Word64 binomialsCache $ \binomialsPtr ->
    mk_fixed_hamming_state_to_index_kernel
      (fromIntegral numberSites)
      (fromIntegral hammingWeight)
      binomialsPtr

destroyFixedHammingStateToIndexKernel :: FunPtr RawStateToIndexKernel -> IO ()
destroyFixedHammingStateToIndexKernel = freeFunPtrClosure

invokeFixedHammingStateToIndexKernel :: FunPtr RawStateToIndexKernel -> S.Vector Word64 -> IO (S.Vector Int64)
invokeFixedHammingStateToIndexKernel funPtr basisStates =
  withHalideBuffer @1 @Word64 basisStates $ \basisStatesBuf ->
    allocaCpuBuffer [S.length basisStates] $ \indicesBuf -> do
      toFun_fixed_hamming_state_to_index_kernel funPtr (castPtr basisStatesBuf) (castPtr indicesBuf)
      S.fromList <$> peekToList indicesBuf

ls_hs_fixed_hamming_state_to_index :: Int64 -> Ptr Word64 -> Ptr Int64 -> IO ()
ls_hs_fixed_hamming_state_to_index batchSize states indices = do
  let dim = fromIntegral binomialsCache.dmRows
  S.unsafeWith binomialsCache.dmData $ \binomials ->
    [CU.block| void {
      uint64_t const* nchoosek = $(uint64_t const* binomials);
      uint64_t const ld_nchoosek = $(int dim);
      int64_t const batch_size = $(int64_t batchSize);
      uint64_t const* states = $(uint64_t const* states);
      int64_t* indices = $(int64_t* indices);

      for (int64_t batch_idx = 0; batch_idx < batch_size; ++batch_idx) {
        uint64_t state = states[batch_idx];
        int k = 0;
        int64_t index = 0;

        while (state) {
          int const n = __builtin_ctzl(state);
          ++k;
          if (k <= n) index += nchoosek[k*ld_nchoosek + n];
          state &= state-1;
        }

        indices[batch_idx] = index;
      }
    } |]

ls_hs_fixed_hamming_index_to_state :: CInt -> CInt -> Int64 -> Ptr Int64 -> Ptr Word64 -> IO ()
ls_hs_fixed_hamming_index_to_state numberSites hammingWeight batchSize indices states = do
  let dim = fromIntegral binomialsCache.dmRows
  S.unsafeWith binomialsCache.dmData $ \binomials ->
    [CU.block| void {
      uint64_t const* nchoosek = $(uint64_t const* binomials);
      uint64_t const ld_nchoosek = $(int dim);
      int const hamming_weight = $(int hammingWeight);
      int const number_sites = $(int numberSites);
      int64_t const batch_size = $(int64_t batchSize);
      int64_t const* indices = $(int64_t const* indices);
      uint64_t* states = $(uint64_t* states);

      for (int64_t batch_idx = 0; batch_idx < batch_size; ++batch_idx) {
        int64_t index = indices[batch_idx];
        uint64_t state = 0;
        int k = hamming_weight;
        for (int n = number_sites; n > 0; --n) {
          state <<= 1;
          uint64_t current = (k > n - 1) ? 0 : nchoosek[k*ld_nchoosek + n - 1];
          if (index >= current) {
              index -= current;
              --k;
              state |= 1;
          }
        }
        states[batch_idx] = state;
      }
    } |]