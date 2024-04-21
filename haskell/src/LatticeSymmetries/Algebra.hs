{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module LatticeSymmetries.Algebra
  ( -- * Polynomials
    Scaled (..)
  , Product (..)
  , Sum (..)
  , Polynomial
  , CanScale (..)
  , CommutatorType (..)
  , Algebra (..)
  , simplifyPolynomial
  , HasProperGeneratorType
  , HasProperIndexType
  , IsBasis
  )
where

import Control.Monad.ST (ST, runST)
import Data.List qualified as List
import Data.Ratio
import Data.Vector (Vector)
import Data.Vector.Fusion.Bundle qualified as Bundle (inplace)
import Data.Vector.Fusion.Bundle.Size (toMax)
import Data.Vector.Fusion.Stream.Monadic (Step (..), Stream (..))
import Data.Vector.Generic ((!))
import Data.Vector.Generic qualified as G
import Data.Vector.Generic.Mutable qualified as GM
import Data.Vector.Mutable (MVector)
import GHC.Exts (IsList (..))
import LatticeSymmetries.ComplexRational
import LatticeSymmetries.Generator
import LatticeSymmetries.NonbranchingTerm
import LatticeSymmetries.Utils (sortVectorBy)
import Prettyprinter (Pretty (..))
import Prelude hiding (Product, Sum, identity, toList)

-- | Represents a term of the form @c × g@ where @c@ is typically a scalar and @g@ is some
-- expression.
data Scaled g = Scaled {coeff :: !ComplexRational, term :: !g}
  deriving stock (Eq, Show, Generic)

instance Functor Scaled where
  fmap f (Scaled c g) = Scaled c (f g)

foldScaled :: CanScale ComplexRational b => (a -> b) -> Scaled a -> b
foldScaled f (Scaled c p) = scale c (f p)

-- | A product of @g@s.
newtype Product g = Product {unProduct :: Vector g}
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (IsList, Functor, Semigroup, Foldable)

-- | A sum of @g@s.
newtype Sum g = Sum {unSum :: Vector g}
  deriving stock (Eq, Show, Generic)
  deriving newtype (IsList, Functor, Semigroup, Monoid, Foldable)

-- | A polynomial in variable @g@ over a field @c@.
type Polynomial g = Sum (Scaled (Product g))

-- | Specifies the type of commutator to use for an algebra.
data CommutatorType
  = -- | Commutator \([a, b] = ab - ba\)
    Commutator
  | -- | Anticommutator \(\{a, b\} = ab + ba\)
    Anticommutator
  deriving stock (Show, Eq)

class HasInternalGenerators g where
  isInternalGenerator :: g -> Bool
  expandInternalGenerator :: g -> Sum (Scaled g)

class (Typeable g, Ord g, HasIdentity g, HasNonbranchingRepresentation g, HasInternalGenerators g, Show g)
  => Algebra g where
  -- | The type of commutator this algebra uses.
  --
  -- We have 'Commutator' for spin (or bosonic) systems and 'Anticommutator' for fermionic systems.
  nonDiagonalCommutatorType :: CommutatorType

  -- | Generators of the algebra.
  algebraGenerators :: Vector g

  -- | Check whether a given generator is diagonal.
  isDiagonal :: g -> Bool

  -- | Compute the Hermitian conjugate of a generator
  conjugateGenerator :: g -> g

class Num c => CanScale c a where
  scale :: c -> a -> a

data CombineNeighborsHelper a
  = CombineNeighborsFirst
  | CombineNeighborsPrevious !a
  | CombineNeighborsDone

combineNeighborsImpl :: Monad m => (a -> a -> Bool) -> (a -> a -> a) -> Stream m a -> Stream m a
{-# INLINE combineNeighborsImpl #-}
combineNeighborsImpl equal combine (Stream step s₀) = Stream step' (CombineNeighborsFirst, s₀)
  where
    {-# INLINE step' #-}
    step' (CombineNeighborsFirst, s) = do
      r <- step s
      case r of
        Yield a s' -> pure $ Skip (CombineNeighborsPrevious a, s')
        Skip s' -> pure $ Skip (CombineNeighborsFirst, s')
        Done -> pure Done
    step' (CombineNeighborsPrevious a, s) = do
      r <- step s
      case r of
        Yield b s' ->
          if equal a b
            then pure $ Skip (CombineNeighborsPrevious (combine a b), s')
            else pure $ Yield a (CombineNeighborsPrevious b, s')
        Skip s' -> pure $ Skip (CombineNeighborsPrevious a, s')
        Done -> pure $ Yield a (CombineNeighborsDone, s)
    step' (CombineNeighborsDone, _) = pure Done

combineNeighbors :: G.Vector v a => (a -> a -> Bool) -> (a -> a -> a) -> v a -> v a
combineNeighbors equal combine =
  G.unstream . Bundle.inplace (combineNeighborsImpl equal combine) toMax . G.stream

instance HasNonbranchingRepresentation g => HasNonbranchingRepresentation (Scaled g) where
  nonbranchingRepresentation (Scaled c g) = t {nbtV = c * nbtV t}
    where
      t = nonbranchingRepresentation g

instance HasNonbranchingRepresentation g => HasNonbranchingRepresentation (Product g) where
  nonbranchingRepresentation (Product v)
    | not (G.null v) = G.foldl1' (<>) . G.map nonbranchingRepresentation $ v
    | otherwise =
        -- an empty Product is equivalent to an identity, and identities for all particle types are the same
        nonbranchingRepresentation (Generator (0 :: Int) SpinIdentity)

instance CanScale ComplexRational (CommutatorType, Sum (Scaled g)) where
  scale z (tp, terms) = (tp, scale z terms)

instance Algebra SpinGeneratorType where
  nonDiagonalCommutatorType = Commutator
  algebraGenerators = [SpinIdentity, SpinZ, SpinPlus, SpinMinus, InternalSpinMinusPlus, InternalSpinPlusMinus]
  isDiagonal = \case
    SpinIdentity -> True
    SpinZ -> True
    SpinPlus -> False
    SpinMinus -> False
    InternalSpinMinusPlus -> True
    InternalSpinPlusMinus -> True
  conjugateGenerator = \case
    SpinIdentity -> SpinIdentity
    SpinZ -> SpinZ
    SpinPlus -> SpinMinus
    SpinMinus -> SpinPlus
    InternalSpinMinusPlus -> InternalSpinMinusPlus
    InternalSpinPlusMinus -> InternalSpinPlusMinus

instance Algebra FermionGeneratorType where
  nonDiagonalCommutatorType = Anticommutator
  algebraGenerators = [FermionIdentity, FermionCount, FermionCreate, FermionAnnihilate, InternalFermionAnnihilateCreate]
  isDiagonal g = case g of
    FermionIdentity -> True
    FermionCount -> True
    FermionCreate -> False
    FermionAnnihilate -> False
    InternalFermionAnnihilateCreate -> True
  conjugateGenerator g = case g of
    FermionIdentity -> FermionIdentity
    FermionCount -> FermionCount
    FermionCreate -> FermionAnnihilate
    FermionAnnihilate -> FermionCreate
    InternalFermionAnnihilateCreate -> InternalFermionAnnihilateCreate

instance (Typeable i, Ord i, Show i, Algebra g, HasNonbranchingRepresentation (Generator i g)) => Algebra (Generator i g) where
  nonDiagonalCommutatorType = nonDiagonalCommutatorType @g
  algebraGenerators = error "Algebra instance of (Generator i g) does not define algebraGenerators"
  isDiagonal (Generator _ g) = isDiagonal g
  conjugateGenerator (Generator i g) = Generator i (conjugateGenerator g)

instance CanScale ComplexRational (Scaled g) where
  scale c (Scaled c' g) = Scaled (c * c') g

instance Traversable Product where
  traverse f (Product v) = Product <$> traverse f v

instance CanScale c g => CanScale c (Sum g) where
  scale c (Sum v) = Sum $ G.map (scale c) v

instance Traversable Sum where
  traverse f (Sum v) = Sum <$> traverse f v

instance Num (Polynomial g) where
  (+) = (<>)
  (Sum a) * (Sum b) = Sum $ multiply <$> a <*> b
    where
      multiply (Scaled c g) (Scaled c' g') = Scaled (c * c') (g <> g')
  negate = scale (-1 :: ComplexRational)
  abs = fmap (\(Scaled c g) -> Scaled (abs c) g)
  signum _ = error "Num instance of Sum does not implement signum"
  fromInteger _ = error "Num instance of Sum does not implement fromInteger"

-- | Canonicalize index order
canonicalizeOrderByIndex :: forall i g. (Ord i, Algebra g, Algebra (Generator i g)) => Product (Generator i g) -> Scaled (Product (Generator i g))
canonicalizeOrderByIndex t0 = runST $ do
  v <- G.thaw (unProduct t0)
  c <- go v False (1 :: ComplexRational) (0 :: Int)
  Scaled c . Product <$> G.unsafeFreeze v
  where
    size = G.length (unProduct t0)
    commutatorToSign tp = case tp of
      Commutator -> 1
      Anticommutator -> -1
    -- This is essentially bubble sort
    go :: MVector s (Generator i g) -> Bool -> ComplexRational -> Int -> ST s ComplexRational
    go !v !keepGoing !c !k
      | k < size - 1 = do
          ga@(Generator ia _) <- GM.read v k
          gb@(Generator ib _) <- GM.read v (k + 1)
          -- This pattern match will fail if commute ga gb generates some
          -- extra terms. However, it should never happen because we're
          -- always swapping elements at different indices
          let commutator
                | isDiagonal ga || isDiagonal gb = Commutator
                | otherwise = nonDiagonalCommutatorType @g
          if ia > ib
            then do
              -- swapping elements
              GM.write v k gb
              GM.write v (k + 1) ga
              go v True (commutatorToSign commutator * c) (k + 1)
            else go v keepGoing c (k + 1)
      | keepGoing = go v False c 0
      | otherwise = pure c

simplifyViaNonbranchingRepresentation :: (HasCallStack, Algebra g) => Product g -> Scaled g
simplifyViaNonbranchingRepresentation p
  | c == 0 = Scaled 0 (G.head algebraGenerators)
  | G.length x /= 1 = error $ "failed to simplify " <> show p <> "; x = " <> show x
  | otherwise = Scaled c (G.head x)
  where
    x = G.filter (\g -> nonbranchingRepresentation g == r) algebraGenerators
    (c, r) = extractScale (nonbranchingRepresentation p)
    extractScale t = (t.nbtV, t {nbtV = 1})

-- | Reduce the degree of a product of terms that belong to the same site.
simplifyProductNoIndices :: forall g i. Algebra g => Product (Generator i g) -> Scaled (Generator i g)
simplifyProductNoIndices (Product v)
  | G.null v = error "simplifyProductNoIndices does not work on empty Products"
  | otherwise = Scaled c (Generator i g)
  where
    (Generator i _) = G.head v
    (Scaled c g) = simplifyViaNonbranchingRepresentation . Product $ (\(Generator _ g) -> g) <$> v

instance HasInternalGenerators SpinGeneratorType where
  isInternalGenerator x = case x of
    InternalSpinMinusPlus -> True
    InternalSpinPlusMinus -> True
    _ -> False
  expandInternalGenerator x = case x of
    InternalSpinMinusPlus ->
      Sum [Scaled (ComplexRational (1 % 2) 0) SpinIdentity, Scaled (ComplexRational ((-1) % 2) 0) SpinZ]
    InternalSpinPlusMinus ->
      Sum [Scaled (ComplexRational (1 % 2) 0) SpinIdentity, Scaled (ComplexRational (1 % 2) 0) SpinZ]
    _ -> Sum [Scaled 1 x]

instance HasInternalGenerators FermionGeneratorType where
  isInternalGenerator x = case x of
    InternalFermionAnnihilateCreate -> True
    _ -> False
  expandInternalGenerator x = case x of
    InternalFermionAnnihilateCreate ->
      Sum [Scaled 1 FermionIdentity, Scaled (-1) FermionCount]
    _ -> Sum [Scaled 1 x]

instance HasInternalGenerators g => HasInternalGenerators (Generator i g) where
  isInternalGenerator (Generator _ x) = isInternalGenerator x
  expandInternalGenerator (Generator i x) = fmap (Generator i) <$> expandInternalGenerator x

containsInternalGenerators :: HasInternalGenerators g => Product (Generator i g) -> Bool
containsInternalGenerators (Product v) = G.any (\(Generator _ g) -> isInternalGenerator g) v

expandProduct :: forall g. HasIdentity g => Product (Sum (Scaled g)) -> Polynomial g
expandProduct (Product terms) = Sum $ fmap multiply . G.mapM unSum $ terms
  where
    multiply :: Vector (Scaled g) -> Scaled (Product g)
    multiply ts =
      let !z = product $ (.coeff) <$> ts
          !xs = Product $ G.filter (not . isIdentity) $ (.term) <$> ts
       in Scaled z xs

expandInternalsInProducts :: forall i g. (HasIdentity g, HasInternalGenerators g) => Polynomial (Generator i g) -> Polynomial (Generator i g)
expandInternalsInProducts (Sum ts) = Sum $ G.concatMap f ts
  where
    f :: Scaled (Product (Generator i g)) -> Vector (Scaled (Product (Generator i g)))
    f x
      | containsInternalGenerators x.term = unSum $
        foldScaled (expandProduct . Product . fmap expandInternalGenerator . unProduct) x
      | otherwise = [x]

-- | Simplify a product of terms. This may introduce internal generators into the product
simplifyProductAddingInternals :: forall i g. (Ord i, Algebra g, Algebra (Generator i g)) => Product (Generator i g) -> Scaled (Product (Generator i g))
simplifyProductAddingInternals p =
  scale sign
    . multiply
    . fmap (simplifyProductNoIndices . Product)
    . G.groupBy (\(Generator i _) (Generator j _) -> i == j)
    $ terms
  where
    (Scaled sign (Product terms)) = canonicalizeOrderByIndex p
    multiply :: [Scaled (Generator i g)] -> Scaled (Product (Generator i g))
    multiply ts =
      let !coeff = product . fmap (.coeff) $ ts
          !xs = Product . G.fromList . filter (not . isIdentity) . fmap (.term) $ ts
       in Scaled coeff xs

collectTerms :: Eq g => Sum (Scaled g) -> Sum (Scaled g)
collectTerms = Sum . dropZeros . combine . unSum
  where
    dropZeros = G.filter (\x -> x.coeff /= 0)
    combine = combineNeighbors (\a b -> a.term == b.term) (\a b -> Scaled (a.coeff + b.coeff) a.term)

reorderTerms :: Ord g => Sum (Scaled g) -> Sum (Scaled g)
reorderTerms = Sum . sortVectorBy (comparing (.term)) . unSum

simplifyPolynomial :: forall g i. (Ord i, Algebra g, HasInternalGenerators g, Algebra (Generator i g)) => Polynomial (Generator i g) -> Polynomial (Generator i g)
simplifyPolynomial =
    (collectTerms . reorderTerms)
    . expandInternalsInProducts
    . (collectTerms . reorderTerms)
    . fmap (foldScaled simplifyProductAddingInternals)

class IsGeneratorType (GeneratorType t) => HasProperGeneratorType t

instance IsGeneratorType (GeneratorType t) => HasProperGeneratorType t

class IsIndexType (IndexType t) => HasProperIndexType t

instance IsIndexType (IndexType t) => HasProperIndexType t

type IsGeneratorType g = (Eq g, Ord g, Pretty g, Algebra g)

type IsIndexType i = (Eq i, Ord i {-HasSiteIndex i,-}, Pretty i)

class
  ( Typeable t
  , HasProperGeneratorType t
  , HasProperIndexType t
  , Pretty (Generator (IndexType t) (GeneratorType t))
  , Algebra (Generator (IndexType t) (GeneratorType t))
  ) =>
  IsBasis t

instance IsBasis 'SpinTy

instance IsBasis 'SpinfulFermionTy

instance IsBasis 'SpinlessFermionTy
