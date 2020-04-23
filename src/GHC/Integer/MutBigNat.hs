{- |
Module      : GHC.Integer.MutBigNat
Description : Mutable interface to GMP byte arrays.
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UnboxedTuples #-}

module GHC.Integer.MutBigNat where

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
--import Data.Bits
import GHC.Exts
--import GHC.Natural
import GHC.Integer.GMP.Internals
import Control.Monad.ST (ST, runST)

-- primitive
import Control.Monad.Primitive (PrimMonad(..), primitive_)
import Data.Primitive.Types (Prim(..))

----------------------------------------------------------------------
-- More operations on BigNat

-- | Construct a 1-limb 'BigNat'.
singleBigNat :: Word -> BigNat
singleBigNat (W# w#) = wordToBigNat w#

-- | Read a limb from an immutable array.
indexBigNat :: BigNat -> Int -> Word
{-# INLINE indexBigNat #-}
indexBigNat (BN# arr#) (I# i#) = indexByteArray# arr# i#

-- | Return the number of limbs in a 'BigNat'.
sizeofBigNat :: BigNat -> Int
{-# INLINE sizeofBigNat #-}
sizeofBigNat bn = I# (sizeofBigNat# bn)

----------------------------------------------------------------------

data MutBigNat s = MBN# !(MutableByteArray# s)

-- | Create a new mutable BigNat with the given number of limbs. The
-- underlying memory is left uninitialized.
newBigNat :: Int -> ST s (MutBigNat s)
{-# INLINE newBigNat #-}
newBigNat (I# n#) =
  primitive
  (\s# ->
      case newByteArray# (toByteOffset# n#) s# of
        (# s'#, arr# #) -> (# s'#, MBN# arr# #)
  )

-- | Read a limb from a mutable array.
readBigNat :: MutBigNat s -> Int -> ST s Word
{-# INLINE readBigNat #-}
readBigNat (MBN# arr#) (I# i#) =
  primitive (readByteArray# arr# i#)

-- | Write an element to the given index.
writeBigNat :: MutBigNat s -> Int -> Word -> ST s ()
{-# INLINE writeBigNat #-}
writeBigNat (MBN# arr#) (I# i#) x =
  primitive_ (writeByteArray# arr# i# x)

copyBigNat ::
  BigNat      {- ^ source array    -} ->
  Int         {- ^ source offset   -} ->
  MutBigNat s {- ^ target array    -} ->
  Int         {- ^ target offset   -} ->
  Int         {- ^ number of limbs -} ->
  ST s ()
copyBigNat (BN# ba#) (I# ofs_ba#) (MBN# mba#) (I# ofs_mba#) (I# len#) =
  primitive_
  (copyByteArray#
    ba# (toByteOffset# ofs_ba#)
    mba# (toByteOffset# ofs_mba#)
    (toByteOffset# len#))

-- | Convert a mutable limb array to an immutable one without copying. The
-- array should not be modified after the conversion.
unsafeFreezeBigNat :: MutBigNat s -> ST s BigNat
{-# INLINE unsafeFreezeBigNat #-}
unsafeFreezeBigNat (MBN# arr#) =
  primitive
  (\s# ->
     case unsafeFreezeByteArray# arr# s# of
       (# s'#, arr'# #) -> (# s'#, BN# arr'# #)
  )

toByteOffset :: Int -> Int
{-# INLINE toByteOffset #-}
toByteOffset (I# i#) = I# (i# `uncheckedIShiftL#` GMP_LIMB_SHIFT#)

toByteOffset# :: Int# -> Int#
{-# INLINE toByteOffset# #-}
toByteOffset# i# = i# `uncheckedIShiftL#` GMP_LIMB_SHIFT#
