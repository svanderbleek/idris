module Ch3

import Data.Vect

allLengths : Vect n String -> Vect n Nat
allLengths [] = []
allLengths (x :: xs) = length x :: allLengths xs

insert :
  Ord a =>
  (x : a) -> (sorted : Vect n a) -> Vect (S n) a
insert x [] = [x]
insert x (y :: xs) =
  case x < y of
    False => y :: insert x xs
    True => x :: y :: xs

insertionSort : Ord a => Vect n a -> Vect n a
insertionSort [] = []
insertionSort (x :: xs) =
  insert x (insertionSort xs)

length' : List a -> Nat
length' [] = 0
length' (x :: xs) = 1 + length' xs

reverse' : List a -> List a
reverse' [] = []
reverse' (x :: xs) = reverse' xs ++ [x]

map' : (a -> b) -> List a -> List b
map' _ [] = []
map' f (x :: xs) = f x :: map' f xs

map'' : (a -> b) -> Vect n a -> Vect n b
map'' _ [] = []
map'' f (x :: xs) = f x :: map'' f xs

Matrix : Nat -> Nat -> Type -> Type
Matrix n m a = Vect n (Vect m a)

transposeMatrix : Matrix n m a -> Matrix m n a
transposeMatrix [] =
  replicate _ []
transposeMatrix (x :: xs) =
  zipWith (::) x (transposeMatrix xs)

addMatrix : Num a => Matrix n m a -> Matrix n m a -> Matrix n m a
addMatrix [] [] = []
addMatrix (x :: xs) (y :: ys) =
  zipWith (+) x y :: addMatrix xs ys

mulRowsCol : Num a => Matrix n m a -> Vect m a -> Vect n a
mulRowsCol [] _ = []
mulRowsCol (x :: xs) y =
  foldr (+) 0 (zipWith (*) x y) :: mulRowsCol xs y

mulRowsCols : Num a => Matrix n m a -> Matrix p m a -> Matrix p n a
mulRowsCols _ [] = []
mulRowsCols xs (y :: ys) =
   mulRowsCol xs y :: mulRowsCols xs ys

mulMatrix : Num a => Matrix n m a -> Matrix m p a -> Matrix n p a
mulMatrix x y =
  transposeMatrix (mulRowsCols x (transposeMatrix y))
