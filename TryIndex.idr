module TryIndex

import Data.Vect

tryIndex : Integer -> Vect n a -> Maybe a
tryIndex {n} x xs =
  case integerToFin x n of
    Nothing => Nothing
    (Just x) => Just (index x xs)

sumEntries : Num a => (p : Integer) -> Vect n a -> Vect n a -> Maybe a
sumEntries {n} p xs ys =
  case integerToFin p n of
    Nothing => Nothing
    (Just i) => Just (index i xs + index i ys)
