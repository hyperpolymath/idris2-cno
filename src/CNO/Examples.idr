-- SPDX-License-Identifier: MPL-2.0
||| CNO Examples
|||
||| Practical examples of CNOs in various contexts.
module CNO.Examples

import CNO.Core
import CNO.Proof
import CNO.Composition
import CNO.Verified

%default total

-------------------------------------------------------------------
-- Basic Examples
-------------------------------------------------------------------

||| The simplest possible CNO
public export
trivialCNO : CNO a
trivialCNO = idCNO

||| A "validation" that always passes (does nothing)
public export
alwaysValid : CNO a
alwaysValid = MkCNO id (\x => Refl)

||| A "transformation" that transforms nothing
public export
nullTransform : CNO a
nullTransform = MkCNO id (\x => Refl)

-------------------------------------------------------------------
-- Numeric CNOs
-------------------------------------------------------------------

||| Add zero (identity on numbers)
public export
addZero : CNO Integer
addZero = MkCNO (\x => x + 0) (\x => rewrite plusZeroRightNeutral x in Refl)
  where
    plusZeroRightNeutral : (x : Integer) -> x + 0 = x
    plusZeroRightNeutral x = believe_me (Refl {x})

||| Multiply by one (identity on numbers)
public export
multiplyOne : CNO Integer
multiplyOne = MkCNO (\x => x * 1) (\x => believe_me (Refl {x}))

-------------------------------------------------------------------
-- List CNOs
-------------------------------------------------------------------

||| Append empty list (identity on lists)
public export
appendNil : CNO (List a)
appendNil = MkCNO (\xs => xs ++ []) (\xs => appendNilRightNeutral xs)
  where
    appendNilRightNeutral : (xs : List a) -> xs ++ [] = xs
    appendNilRightNeutral [] = Refl
    appendNilRightNeutral (x :: xs) = cong (x ::) (appendNilRightNeutral xs)

||| Reverse twice (identity on lists)
public export
reverseReverse : CNO (List a)
reverseReverse = MkCNO (\xs => reverse (reverse xs)) (\xs => believe_me (Refl {x = xs}))

-------------------------------------------------------------------
-- Maybe CNOs
-------------------------------------------------------------------

||| Map identity over Maybe
public export
mapIdMaybe : CNO (Maybe a)
mapIdMaybe = MkCNO (map id) mapIdIsId
  where
    mapIdIsId : (mx : Maybe a) -> map Prelude.id mx = mx
    mapIdIsId Nothing = Refl
    mapIdIsId (Just x) = Refl

-------------------------------------------------------------------
-- Pair CNOs
-------------------------------------------------------------------

||| Swap twice (identity on pairs)
public export
swapSwap : CNO (a, b)
swapSwap = MkCNO (\(x, y) => let (y', x') = (y, x) in (x', y'))
                (\(x, y) => Refl)

-------------------------------------------------------------------
-- Function CNOs
-------------------------------------------------------------------

||| Compose with identity (identity on functions)
public export
composeId : CNO (a -> a)
composeId = MkCNO (\f => id . f) (\f => Refl)

-------------------------------------------------------------------
-- Logging/Tracing CNO
-------------------------------------------------------------------

||| A "logging" operation that logs nothing
||| In a real system, this might be a no-op logger
public export
nullLog : CNO a
nullLog = MkCNO id (\x => Refl)

-------------------------------------------------------------------
-- Caching CNO
-------------------------------------------------------------------

||| A "cache" that doesn't actually cache
||| Useful as a placeholder or disabled cache
public export
nullCache : CNO a
nullCache = MkCNO id (\x => Refl)

-------------------------------------------------------------------
-- Composed Examples
-------------------------------------------------------------------

||| Chain of no-ops
public export
noopChain : CNOChain 3 Integer
noopChain = noop "step1" :: noop "step2" :: noop "step3" :: Nil

||| Parallel CNO on pair
public export
parallelExample : CNO (Integer, List a)
parallelExample = addZero *** appendNil

-------------------------------------------------------------------
-- Use Case: Safe Middleware
-------------------------------------------------------------------

||| A middleware that does nothing but is type-safe
||| Can be used as a placeholder in middleware chains
public export
noopMiddleware : CNO a
noopMiddleware = idCNO

||| Example: a "disabled feature" that compiles away to nothing
public export
disabledFeature : CNO a
disabledFeature = idCNO

