{- |
Module      : GHC.Integer.Extra
Description : Extra operations on Integer and Natural types.
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UnboxedTuples #-}

module GHC.Integer.Extra where

#include "MachDeps.h"

#if WORD_SIZE_IN_BITS == 64
#define GMP_LIMB_BITS 64
#define GMP_LIMB_SHIFT 3
#elif WORD_SIZE_IN_BITS == 32
#define GMP_LIMB_BITS 32
#define GMP_LIMB_SHIFT 2
#else
#error unsupported WORD_SIZE_IN_BITS config
#endif

-- base
import qualified Control.Exception as X
import Data.Bits
import GHC.Exts
import GHC.Natural
import GHC.Integer.GMP.Internals
import Control.Monad.ST (runST)

-- gmp-integer-extra
import GHC.Integer.GMP.Extra
import GHC.Integer.MutBigNat

-- | @widthNatural x@ returns the width of @x@ in bits; more
-- precisely, the least @n@ such that @x < 2^n@.
widthNatural :: Natural -> Int
widthNatural (NatS# x#) = I# (widthWord# x#)
widthNatural (NatJ# bn) = I# (widthBigNat# bn)

-- | @widthInteger x@ returns the width of the absolute value of @x@
-- in bits.
widthInteger :: Integer -> Int
widthInteger (S# x#)  = I# (widthInt# x#)
widthInteger (Jp# bn) = I# (widthBigNat# bn)
widthInteger (Jn# bn) = I# (widthBigNat# bn)

truncateNatural :: Int -> Natural -> Natural
truncateNatural (I# i#) (NatS# x#) = NatS# (truncateWord# i# x#)
truncateNatural (I# i#) (NatJ# bn) = bigNatToNatural (truncateBigNat i# bn)

truncateInteger :: Int -> Integer -> Integer
truncateInteger (I# i#) (S# x#) = wordToInteger (truncateWord# i# (int2Word# x#))
truncateInteger (I# i#) (Jp# bn) = bigNatToInteger (truncateBigNat i# bn)
truncateInteger (I# i#) (Jn# bn) = bigNatToInteger (truncateNegBigNat i# bn)

truncateInteger' :: Int -> Integer -> Integer
truncateInteger' (I# i#) (S# x#) = wordToInteger (truncateWord# i# (int2Word# x#))
truncateInteger' (I# i#) (Jp# bn) = bigNatToInteger (truncateBigNat' (I# i#) bn)
truncateInteger' (I# i#) (Jn# bn) = bigNatToInteger (truncateNegBigNat i# bn)

truncateBigNat' :: Int -> BigNat -> BigNat
truncateBigNat' i bn
  | li >= nx = bn -- bignat is already small enough
  | li + 1 == nx, newlimb == limb = bn
  | nx == 1 = singleBigNat newlimb
  | otherwise =
    case newlimb of
      0 ->
        case fmssl bn (li - 1) of
          0 -> zeroBigNat
          n ->
            runST $
            do mbn <- newBigNat n
               copyBigNat bn 0 mbn 0 n
               unsafeFreezeBigNat mbn
      _ ->
        runST $ -- no shrinking
        do mbn <- newBigNat (li + 1)
           copyBigNat bn 0 mbn 0 li
           writeBigNat mbn li newlimb
           unsafeFreezeBigNat mbn
  where
    (li, bi) = i `quotRem` WORD_SIZE_IN_BITS
    limb = indexBigNat bn li
    newlimb = truncateWord bi limb
    nx = sizeofBigNat bn

{-
truncateNegBigNat' :: Int -> BigNat -> BigNat
truncateNegBigNat' i bn
  |
  where
    (li, bi) = i `quotRem` WORD_SIZE_IN_BITS
    lx = flssl bn nx
    nx = sizeofBigNat bn
-- FIXME: We need to subtract 1 and then do bitwise complement up to
-- the given number of bits.
-}

truncateWord :: Int -> Word -> Word
truncateWord i w = w .&. (bit i - 1)

-- find most-sig set limb, starting at given index
fmssl :: BigNat -> Int -> Int
fmssl !bn i0 = go i0
  where
    go i | i < 0                 = 0
         | indexBigNat bn i /= 0 = i + 1
         | otherwise             = go (i - 1)

-- find least-sig set limb, stopping at given index
flssl :: BigNat -> Int -> Int
flssl !bn l = go 0
  where
    go i | i >= l                = l
         | indexBigNat bn i /= 0 = i
         | otherwise             = go (i + 1)

{-
truncateBigNat' :: Int# -> BigNat -> BigNat
truncateBigNat' i# bn
  | isTrue# (li# >=# nx#) = bn -- bignat is already small enough
  | isTrue# (li# +# 1# ==# nx#)
  , isTrue# (newlimb# `eqWord#` limb#) = bn
  | isTrue# (nx# ==# 1#) = wordToBigNat newlimb#
  | True =
      case newlimb# of
        0## -> do -- most-sig limb became zero -> result has less limbs
            case fmssl bn (li# -# 1#) of
              0# -> zeroBigNat
              n# -> runS $ do
                  mbn <- newBigNat# n#
                  _ <- copyWordArray bn 0# mbn 0# n#
                  unsafeFreezeBigNat# mbn
        _ -> runS $ do -- no shrinking
            mbn <- newBigNat# (li# +# 1#)
            _ <- copyWordArray bn 0# mbn 0# li#
            _ <- svoid (writeBigNat# mbn li# newlimb#)
            unsafeFreezeBigNat# mbn
  where
    !(# li#, bi# #) = quotRemInt# i# GMP_LIMB_BITS#
    limb# = indexBigNat# bn li#
    newlimb# = uncheckedTruncateWord# bi# limb#
    nx# = sizeofBigNat# bn
-}

----------------------------------------------------------------------------
-- copied from GHC.Natural

-- | Convert 'BigNat' to 'Natural'.
-- Throws 'Underflow' if passed a 'nullBigNat'.
bigNatToNatural :: BigNat -> Natural
bigNatToNatural bn
  | isTrue# (sizeofBigNat# bn ==# 1#) = NatS# (bigNatToWord bn)
  | isTrue# (isNullBigNat# bn)        = underflowError
  | True                              = NatJ# bn

{-# NOINLINE underflowError #-}
underflowError :: a
underflowError = raise# underflowException

underflowException :: X.SomeException
underflowException = X.toException X.Underflow

----------------------------------------------------------------------------
-- Primitive arrays
{-
fromBigNat :: BigNat -> PrimArray Word
fromBigNat (BN# ba#) = PrimArray ba#

toBigNat :: PrimArray Word -> BigNat
toBigNat (PrimArray ba#) = BN# ba#

createPrimArray :: (forall s. ST s (MutablePrimArray s a)) -> PrimArray a
createPrimArray f = runST (f Prelude.>>= unsafeFreezePrimArray)

createBigNatFromMutablePrimArray :: (forall s. ST s (MutablePrimArray s Word)) -> BigNat
createBigNatFromMutablePrimArray f = toBigNat (createPrimArray f)

createBigNatFromMutablePrimArray' :: Int -> (forall s. MutablePrimArray s Word -> ST s ()) -> BigNat
createBigNatFromMutablePrimArray' n f = toBigNat (newPrimArray n >>= f)
-}
