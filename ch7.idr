module Ch7

occurrences : (Eq ty) => (item : ty) -> (values : List ty) -> Nat
occurrences item =
  sum . map count
  where
    count val = if item == val then 1 else 0

data Matter
  = Solid
  | Liquid
  | Gas

data Shape
  = Triangle Double Double
  | Rectangle Double Double
  | Circle Double

Eq Shape where
  (Triangle x y) == (Triangle z w) = x == z && y == w
  (Rectangle x y) == (Triangle z w) = x == z && y == w
  (Circle x) == (Circle y ) = x == y
  _ == _ = False

area : Shape -> Double
area (Triangle x y) = 1/2 * x * y
area (Rectangle x y) = x * y
area (Circle x) = pi * x * x

Ord Shape where
  compare s1 s2 = compare (area s1) (area s2)

data Expr num
  = Val num
  | Add (Expr num) (Expr num)
  | Mul (Expr num) (Expr num)
  | Sub (Expr num) (Expr num)
  | Abs (Expr num)

Num ty => Num (Expr ty) where
  (+) = Add
  (*) = Mul
  fromInteger = Val . fromInteger

Neg ty => Neg (Expr ty) where
  negate x = 0 - x
  (-) = Sub
  abs = Abs

Show ty => Show (Expr ty) where
  show (Val x) = show x
  show (Add x y) = "(" ++ show x ++ " + " ++ show y ++ ")"
  show (Mul x y) = "(" ++ show x ++ " * " ++ show y ++ ")"
  show (Sub x y) = "(" ++ show x ++ " - " ++ show y ++ ")"
  show (Abs x) = "abs" ++ show x

eval : (Num num, Neg num) => Expr num -> num
eval (Val x) = x
eval (Add x y) = eval x + eval y
eval (Mul x y) = eval x * eval y
eval (Sub x y) = eval x - eval y
eval (Abs x) = abs (eval x)

(Eq ty, Num ty, Neg ty) => Eq (Expr ty) where
  a == b = (eval a) == (eval b)

(Num ty, Neg ty) => Cast (Expr ty) ty where
  cast = eval

data Tree elem
  = Empty
  | Node (Tree elem) elem (Tree elem)

Foldable Tree where
  foldr f a Empty = a
  foldr f a (Node l e r) =
    f e (foldr f (foldr f a l) r)

Functor Expr where
  map f (Val x) = Val $ f x
  map f (Add x y) = Add (map f x) (map f y)
  map f (Mul x y) = Mul (map f x) (map f y)
  map f (Sub x y) = Sub (map f x) (map f y)
  map f (Abs x) = Abs $ map f x

data Vect : Nat -> Type -> Type where
  Nil : Vect Z a
  (::) : (x : a) -> (xs : Vect k a) -> Vect (S k) a

Eq e => Eq (Vect n e) where
  [] == [] = True
  (x :: xs) == (y :: ys) = x == y && xs == ys

Foldable (Vect n) where
  foldr f a [] = a
  foldr f a (x :: xs) = f x (foldr f a xs)
