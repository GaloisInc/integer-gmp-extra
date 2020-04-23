{- |
Module      : GHC.Integer.GMP.Extra
Description : Extra operations on GMP byte arrays.
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE UnboxedTuples #-}

module GHC.Integer.GMP.Extra
  ( widthWord#
  , widthBigNat#
  , widthInt#
  , truncateWord#
  , truncateBigNat
  , truncateNegBigNat

  , copyWordArray
  ) where

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
import GHC.Exts

-- ghc-prim
-- import GHC.Classes
-- import GHC.Magic
-- import GHC.Prim
import GHC.Types

-- integer-gmp
import GHC.Integer.GMP.Internals

widthWord# :: Word# -> Int#
widthWord# x# = WORD_SIZE_IN_BITS# -# word2Int# (clz# x#)

widthInt# :: Int# -> Int#
widthInt# x#
  | isTrue# (0# <=# x#) = widthWord# (int2Word# x#)
  | True                = widthWord# (int2Word# (negateInt# x#))

widthBigNat# :: BigNat -> Int#
widthBigNat# (BN# ba#) =
  (limbs# *# WORD_SIZE_IN_BITS#) -# word2Int# zeros#
  where
    bytes# = sizeofByteArray# ba#
    limbs# = bytes# `uncheckedIShiftRL#` GMP_LIMB_SHIFT#
    zeros# = clz# (indexWordArray# ba# (limbs# -# 1#))


-- indexWordArray# :: ByteArray# -> Int# -> Word#
-- clz# :: Word# -> Word#
-- uncheckedShiftRL# :: Word# -> Int# -> Word#

truncateWord# :: Int# -> Word# -> Word#
truncateWord# i# w#
  | isTrue# (i# >=# WORD_SIZE_IN_BITS#) = w#
  | True = uncheckedTruncateWord# i# w#

uncheckedTruncateWord# :: Int# -> Word# -> Word#
uncheckedTruncateWord# i# w# =
  w# `and#` (bitWord# i# `minusWord#` 1##)

truncateBigNat :: Int# -> BigNat -> BigNat
truncateBigNat i# bn
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

truncateNegBigNat :: Int# -> BigNat -> BigNat
truncateNegBigNat i# bn = truncateBigNat i# bn
-- FIXME: We need to subtract 1 and then do bitwise complement up to
-- the given number of bits.

----------------------------------------------------------------------------
-- BigNat-wrapped ByteArray#-primops
-- copied from GHC.Integer.Type in package integer-gmp
{---------------------
-- | Return number of limbs contained in 'BigNat'.
sizeofBigNat# :: BigNat -> GmpSize#
sizeofBigNat# (BN# x#)
    = sizeofByteArray# x# `uncheckedIShiftRL#` GMP_LIMB_SHIFT#
-}
data MutBigNat s = MBN# !(MutableByteArray# s)
{-
getSizeofMutBigNat# :: MutBigNat s -> State# s -> (# State# s, GmpSize# #)
--getSizeofMutBigNat# :: MutBigNat s -> S s GmpSize#
getSizeofMutBigNat# (MBN# x#) s =
    case getSizeofMutableByteArray# x# s of
        (# s', n# #) -> (# s', n# `uncheckedIShiftRL#` GMP_LIMB_SHIFT# #)
-}
newBigNat# :: GmpSize# -> S s (MutBigNat s)
newBigNat# limbs# s =
    case newByteArray# (limbs# `uncheckedIShiftL#` GMP_LIMB_SHIFT#) s of
        (# s', mba# #) -> (# s', MBN# mba# #)

writeBigNat# :: MutBigNat s -> GmpSize# -> GmpLimb# -> State# s -> State# s
writeBigNat# (MBN# mba#) = writeWordArray# mba#
{-
-- | Extract /n/-th (0-based) limb in 'BigNat'.
-- /n/ must be less than size as reported by 'sizeofBigNat#'.
indexBigNat# :: BigNat -> GmpSize# -> GmpLimb#
indexBigNat# (BN# ba#) = indexWordArray# ba#
-}
unsafeFreezeBigNat# :: MutBigNat s -> S s BigNat
unsafeFreezeBigNat# (MBN# mba#) s = case unsafeFreezeByteArray# mba# s of
                                      (# s', ba# #) -> (# s', BN# ba# #)
{-
resizeMutBigNat# :: MutBigNat s -> GmpSize# -> S s (MutBigNat s)
resizeMutBigNat# (MBN# mba0#) nsz# s
  | isTrue# (bsz# ==# n#) = (# s', MBN# mba0# #)
  | True =
    case resizeMutableByteArray# mba0# bsz# s' of
        (# s'', mba# #) -> (# s'', MBN# mba# #)
  where
    bsz# = nsz# `uncheckedIShiftL#` GMP_LIMB_SHIFT#
    !(# s', n# #) = getSizeofMutableByteArray# mba0# s

shrinkMutBigNat# :: MutBigNat s -> GmpSize# -> State# s -> State# s
shrinkMutBigNat# (MBN# mba0#) nsz# s
  | isTrue# (bsz# ==# n#) = s' -- no-op
  | True                  = shrinkMutableByteArray# mba0# bsz# s'
  where
    bsz# = nsz# `uncheckedIShiftL#` GMP_LIMB_SHIFT#
    !(# s', n# #) = getSizeofMutableByteArray# mba0# s

unsafeSnocFreezeBigNat# :: MutBigNat s -> GmpLimb# -> S s BigNat
unsafeSnocFreezeBigNat# mbn0@(MBN# mba0#) limb# s = go s'
  where
    n#   = nb0# `uncheckedIShiftRL#` GMP_LIMB_SHIFT#
    !(# s', nb0# #) = getSizeofMutableByteArray# mba0# s
    go = do
        (MBN# mba#) <- resizeMutBigNat# mbn0 (n# +# 1#)
        _ <- svoid (writeWordArray# mba# n# limb#)
        unsafeFreezeBigNat# (MBN# mba#)

-- | May shrink underlyng 'ByteArray#' if needed to satisfy BigNat invariant
unsafeRenormFreezeBigNat# :: MutBigNat s -> S s BigNat
unsafeRenormFreezeBigNat# mbn s
  | isTrue# (n0# ==# 0#)  = (# s'', nullBigNat #)
  | isTrue# (n#  ==# 0#)  = (# s'', zeroBigNat #)
  | isTrue# (n#  ==# n0#) = (unsafeFreezeBigNat# mbn) s''
  | True                  = (unsafeShrinkFreezeBigNat# mbn n#) s''
  where
    !(# s', n0# #) = getSizeofMutBigNat# mbn s
    !(# s'', n# #) = normSizeofMutBigNat'# mbn n0# s'

-- | Shrink MBN
unsafeShrinkFreezeBigNat# :: MutBigNat s -> GmpSize# -> S s BigNat
unsafeShrinkFreezeBigNat# x@(MBN# xmba) 1#
    = \s -> case readWordArray# xmba 0# s of
        (# s', w#   #) -> freezeOneLimb w# s'
  where
    freezeOneLimb 0## = return zeroBigNat
    freezeOneLimb 1## = return oneBigNat
    freezeOneLimb w# | isTrue# (not# w# `eqWord#` 0##) = return czeroBigNat
    freezeOneLimb _   = do
        _ <- svoid (shrinkMutBigNat# x 1#)
        unsafeFreezeBigNat# x
unsafeShrinkFreezeBigNat# x y# = do
    _ <- svoid (shrinkMutBigNat# x y#)
    unsafeFreezeBigNat# x
-}

copyWordArray# :: ByteArray# -> Int# -> MutableByteArray# s -> Int# -> Int#
                  -> State# s -> State# s
copyWordArray# src src_ofs dst dst_ofs len
  = copyByteArray# src (src_ofs `uncheckedIShiftL#` GMP_LIMB_SHIFT#)
                   dst (dst_ofs `uncheckedIShiftL#` GMP_LIMB_SHIFT#)
                   (len `uncheckedIShiftL#` GMP_LIMB_SHIFT#)

copyWordArray :: BigNat -> Int# -> MutBigNat s -> Int# -> Int# -> S s ()
copyWordArray (BN# ba#) ofs_ba# (MBN# mba#) ofs_mba# len#
  = svoid (copyWordArray# ba# ofs_ba# mba# ofs_mba# len#)
{-
clearWordArray# :: MutableByteArray# s -> Int# -> Int# -> State# s -> State# s
clearWordArray# mba ofs len
  = setByteArray# mba (ofs `uncheckedIShiftL#` GMP_LIMB_SHIFT#)
                      (len `uncheckedIShiftL#` GMP_LIMB_SHIFT#) 0#

-- | Version of 'normSizeofMutBigNat'#' which scans all allocated 'MutBigNat#'
normSizeofMutBigNat# :: MutBigNat s -> State# s -> (# State# s, Int# #)
normSizeofMutBigNat# mbn@(MBN# mba) s = normSizeofMutBigNat'# mbn sz# s'
  where
    !(# s', n# #) = getSizeofMutableByteArray# mba s
    sz# = n# `uncheckedIShiftRA#` GMP_LIMB_SHIFT#

-- | Find most-significant non-zero limb and return its index-position
-- plus one. Start scanning downward from the initial limb-size
-- (i.e. start-index plus one) given as second argument.
--
-- NB: The 'normSizeofMutBigNat' of 'zeroBigNat' would be @0#@
normSizeofMutBigNat'# :: MutBigNat s -> GmpSize#
                         -> State# s -> (# State# s, GmpSize# #)
normSizeofMutBigNat'# (MBN# mba) = go
  where
    go  0# s = (# s, 0# #)
    go i0# s = case readWordArray# mba (i0# -# 1#) s of
        (# s', 0## #) -> go (i0# -# 1#) s'
        (# s', _  #) -> (# s', i0# #)

-- | Construct 'BigNat' from existing 'ByteArray#' containing /n/
-- 'GmpLimb's in least-significant-first order.
--
-- If possible 'ByteArray#', will be used directly (i.e. shared
-- /without/ cloning the 'ByteArray#' into a newly allocated one)
--
-- Note: size parameter (times @sizeof(GmpLimb)@) must be less or
-- equal to its 'sizeofByteArray#'.
byteArrayToBigNat# :: ByteArray# -> GmpSize# -> BigNat
byteArrayToBigNat# ba# n0#
  | isTrue# (n#  ==# 0#)    = zeroBigNat
  | isTrue# (baszr# ==# 0#) -- i.e. ba# is multiple of limb-size
  , isTrue# (baszq# ==# n#) = (BN# ba#)
  | True = runS $ \s ->
      let !(# s', mbn@(MBN# mba#) #) = newBigNat# n# s
          !(# s'', ba_sz# #) = getSizeofMutableByteArray# mba# s'
          go = do _ <- svoid (copyByteArray# ba# 0# mba# 0# ba_sz# )
                  unsafeFreezeBigNat# mbn
      in go s''
  where
    !(# baszq#, baszr# #) = quotRemInt# (sizeofByteArray# ba#) GMP_LIMB_BYTES#

    n#  = fmssl (BN# ba#) (n0# -# 1#)

-- | Read 'Integer' (without sign) from memory location at @/addr/@ in
-- base-256 representation.
--
-- @'importIntegerFromAddr' /addr/ /size/ /msbf/@
--
-- See description of 'importIntegerFromByteArray' for more details.
--
-- @since 1.0.0.0
importIntegerFromAddr :: Addr# -> Word# -> Int# -> IO Integer
importIntegerFromAddr addr len msbf = IO $ do
    bn <- liftIO (importBigNatFromAddr addr len msbf)
    return (bigNatToInteger bn)

-- | Version of 'importIntegerFromAddr' constructing a 'BigNat'
importBigNatFromAddr :: Addr# -> Word# -> Int# -> IO BigNat
importBigNatFromAddr _ 0## _ = IO (\s -> (# s, zeroBigNat #))
importBigNatFromAddr addr len0 1# = IO $ do -- MSBF
    W# ofs <- liftIO (c_scan_nzbyte_addr addr 0## len0)
    let len = len0 `minusWord#` ofs
        addr' = addr `plusAddr#` (word2Int# ofs)
    importBigNatFromAddr# addr' len 1#
importBigNatFromAddr addr len0 _ = IO $ do -- LSBF
    W# len <- liftIO (c_rscan_nzbyte_addr addr 0## len0)
    importBigNatFromAddr# addr len 0#

foreign import ccall unsafe "integer_gmp_scan_nzbyte"
    c_scan_nzbyte_addr :: Addr# -> Word# -> Word# -> IO Word

foreign import ccall unsafe "integer_gmp_rscan_nzbyte"
    c_rscan_nzbyte_addr :: Addr# -> Word# -> Word# -> IO Word

-- | Helper for 'importBigNatFromAddr'
importBigNatFromAddr# :: Addr# -> Word# -> Int# -> S RealWorld BigNat
importBigNatFromAddr# _ 0## _ = return zeroBigNat
importBigNatFromAddr# addr len msbf = do
    mbn@(MBN# mba#) <- newBigNat# n#
    () <- liftIO (c_mpn_import_addr mba# addr 0## len msbf)
    unsafeFreezeBigNat# mbn
  where
    -- n = ceiling(len / SIZEOF_HSWORD), i.e. number of limbs required
    n# = (word2Int# len +# (SIZEOF_HSWORD# -# 1#)) `quotInt#` SIZEOF_HSWORD#

foreign import ccall unsafe "integer_gmp_mpn_import"
    c_mpn_import_addr :: MutableByteArray# RealWorld -> Addr# -> Word# -> Word#
                      -> Int# -> IO ()

-- | Read 'Integer' (without sign) from byte-array in base-256 representation.
--
-- The call
--
-- @'importIntegerFromByteArray' /ba/ /offset/ /size/ /msbf/@
--
-- reads
--
-- * @/size/@ bytes from the 'ByteArray#' @/ba/@ starting at @/offset/@
--
-- * with most significant byte first if @/msbf/@ is @1#@ or least
--   significant byte first if @/msbf/@ is @0#@, and
--
-- * returns a new 'Integer'
--
-- @since 1.0.0.0
importIntegerFromByteArray :: ByteArray# -> Word# -> Word# -> Int# -> Integer
importIntegerFromByteArray ba ofs len msbf
    = bigNatToInteger (importBigNatFromByteArray ba ofs len msbf)

-- | Version of 'importIntegerFromByteArray' constructing a 'BigNat'
importBigNatFromByteArray :: ByteArray# -> Word# -> Word# -> Int# -> BigNat
importBigNatFromByteArray _  _    0##  _  = zeroBigNat
importBigNatFromByteArray ba ofs0 len0 1# = runS $ do -- MSBF
    W# ofs <- liftIO (c_scan_nzbyte_bytearray ba ofs0 len0)
    let len = (len0 `plusWord#` ofs0) `minusWord#` ofs
    importBigNatFromByteArray# ba ofs len 1#
importBigNatFromByteArray ba ofs  len0 _  = runS $ do -- LSBF
    W# len <- liftIO (c_rscan_nzbyte_bytearray ba ofs len0)
    importBigNatFromByteArray# ba ofs len 0#

foreign import ccall unsafe "integer_gmp_scan_nzbyte"
    c_scan_nzbyte_bytearray :: ByteArray# -> Word# -> Word# -> IO Word

foreign import ccall unsafe "integer_gmp_rscan_nzbyte"
    c_rscan_nzbyte_bytearray :: ByteArray# -> Word# -> Word# -> IO Word

-- | Helper for 'importBigNatFromByteArray'
importBigNatFromByteArray# :: ByteArray# -> Word# -> Word# -> Int#
                           -> S RealWorld BigNat
importBigNatFromByteArray# _ _ 0## _ = return zeroBigNat
importBigNatFromByteArray# ba ofs len msbf = do
    mbn@(MBN# mba#) <- newBigNat# n#
    () <- liftIO (c_mpn_import_bytearray mba# ba ofs len msbf)
    unsafeFreezeBigNat# mbn
  where
    -- n = ceiling(len / SIZEOF_HSWORD), i.e. number of limbs required
    n# = (word2Int# len +# (SIZEOF_HSWORD# -# 1#)) `quotInt#` SIZEOF_HSWORD#

foreign import ccall unsafe "integer_gmp_mpn_import"
    c_mpn_import_bytearray :: MutableByteArray# RealWorld -> ByteArray# -> Word#
                           -> Word# -> Int# -> IO ()

-- | Test whether all internal invariants are satisfied by 'BigNat' value
--
-- Returns @1#@ if valid, @0#@ otherwise.
--
-- This operation is mostly useful for test-suites and/or code which
-- constructs 'Integer' values directly.
isValidBigNat# :: BigNat -> Int#
isValidBigNat# (BN# ba#)
  = (szq# ># 0#) `andI#` (szr# ==# 0#) `andI#` isNorm#
  where
    isNorm#
      | isTrue# (szq# ># 1#) = (indexWordArray# ba# (szq# -# 1#)) `neWord#` 0##
      | True                 = 1#

    sz# = sizeofByteArray# ba#

    !(# szq#, szr# #) = quotRemInt# sz# GMP_LIMB_BYTES#

-- | Version of 'nextPrimeInteger' operating on 'BigNat's
--
-- @since 1.0.0.0
nextPrimeBigNat :: BigNat -> BigNat
nextPrimeBigNat bn@(BN# ba#) = runS $ do
    mbn@(MBN# mba#) <- newBigNat# n#
    (W# c#) <- liftIO (nextPrime# mba# ba# n#)
    case c# of
        0## -> unsafeFreezeBigNat# mbn
        _   -> unsafeSnocFreezeBigNat# mbn c#
  where
    n# = sizeofBigNat# bn

foreign import ccall unsafe "integer_gmp_next_prime"
  nextPrime# :: MutableByteArray# RealWorld -> ByteArray# -> GmpSize#
                -> IO GmpLimb
---------------}
----------------------------------------------------------------------------
-- monadic combinators for low-level state threading
-- copied from GHC.Integer.Type in package integer-gmp

type S s a = State# s -> (# State# s, a #)

infixl 1 >>=
infixl 1 >>
infixr 0 $

{-# INLINE ($) #-}
($)                     :: (a -> b) -> a -> b
f $ x                   =  f x

{-# INLINE (>>=) #-}
(>>=) :: S s a -> (a -> S s b) -> S s b
(>>=) m k = \s -> case m s of (# s', a #) -> k a s'

{-# INLINE (>>) #-}
(>>) :: S s a -> S s b -> S s b
(>>) m k = \s -> case m s of (# s', _ #) -> k s'

{-# INLINE svoid #-}
svoid :: (State# s -> State# s) -> S s ()
svoid m0 = \s -> case m0 s of s' -> (# s', () #)

{-# INLINE return #-}
return :: a -> S s a
return a = \s -> (# s, a #)

{-# INLINE liftIO #-}
liftIO :: IO a -> S RealWorld a
liftIO (IO m) = m

-- NB: equivalent of GHC.IO.unsafeDupablePerformIO, see notes there
runS :: S RealWorld a -> a
runS m = case runRW# m of (# _, a #) -> a

-- stupid hack
fail :: [Char] -> S s a
fail s = return (raise# s)

----------------------------------------------------------------------------
-- Helpers copied from GHC.Integer.Type in package integer-gmp

-- cmpW# :: Word# -> Word# -> Ordering
-- cmpW# x# y#
--   | isTrue# (x# `ltWord#` y#) = LT
--   | isTrue# (x# `eqWord#` y#) = EQ
--   | True                      = GT
-- {-# INLINE cmpW# #-}

bitWord# :: Int# -> Word#
bitWord# = uncheckedShiftL# 1##
{-# INLINE bitWord# #-}

testBitWord# :: Word# -> Int# -> Int#
testBitWord# w# i# = (bitWord# i# `and#` w#) `neWord#` 0##
{-# INLINE testBitWord# #-}

popCntI# :: Int# -> Int#
popCntI# i# = word2Int# (popCnt# (int2Word# i#))
{-# INLINE popCntI# #-}

-- branchless version
absI# :: Int# -> Int#
absI# i# = (i# `xorI#` nsign) -# nsign
  where
    -- nsign = negateInt# (i# <# 0#)
    nsign = uncheckedIShiftRA# i# (WORD_SIZE_IN_BITS# -# 1#)

-- branchless version
sgnI# :: Int# -> Int#
sgnI# x# = (x# ># 0#) -# (x# <# 0#)

cmpI# :: Int# -> Int# -> Int#
cmpI# x# y# = (x# ># y#) -# (x# <# y#)

minI# :: Int# -> Int# -> Int#
minI# x# y# | isTrue# (x# <=# y#) = x#
            | True                = y#

-- find most-sig set limb, starting at given index
fmssl :: BigNat -> Int# -> Int#
fmssl !bn i0# = go i0#
  where
    go i# | isTrue# (i# <# 0#)                         = 0#
          | isTrue# (neWord# (indexBigNat# bn i#) 0##) = i# +# 1#
          | True                                       = go (i# -# 1#)
