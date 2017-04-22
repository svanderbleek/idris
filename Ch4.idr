module Ch4

import Data.Fin

%default total

data Direction = North | East | South | West

turnClockwise : Direction -> Direction
turnClockwise North = East
turnClockwise East = South
turnClockwise South = West
turnClockwise West = North

||| Represents Shapes
data Shape
  = ||| A triangle, with base and height
  Triangle Double Double
  | ||| A rectangle, with length and height
  Rectangle Double Double
  | ||| A circle, with radius
  Circle Double

area : Shape -> Double
area (Triangle x y) = 0.5 * x * y
area (Rectangle x y) = x * y
area (Circle x) = pi * x * x

data Picture
  = Primitive Shape
  | Combine Picture Picture
  | Rotate Double Picture
  | Translate Double Double Picture

testRectangle : Picture
testRectangle = Primitive (Rectangle 20 10)

testCircle : Picture
testCircle = Primitive (Circle 5)

testTriangle : Picture
testTriangle = Primitive (Triangle 10 10)

testPicture : Picture
testPicture =
  Combine
    (Translate 5 5 testRectangle)
    (Combine
      (Translate 35 5 testCircle)
      (Translate 15 25 testTriangle))

%name Shape shape, shape1, shape2
%name Picture pic, pic1, pic2

pictureArea : Picture -> Double
pictureArea (Primitive shape) = area shape
pictureArea (Combine pic pic1) = pictureArea pic + pictureArea pic1
pictureArea (Rotate _ pic) = pictureArea pic
pictureArea (Translate _ _ pic) = pictureArea pic

data Biggest
  = NoTriangle
  | Size Double

biggestArea : Biggest -> Biggest -> Biggest
biggestArea NoTriangle b =
  b
biggestArea b NoTriangle = b
biggestArea sx@(Size x) sy@(Size y) =
  if x > y then sx else sy

biggestTriangle : Picture -> Biggest
biggestTriangle (Primitive t@(Triangle x y)) =
  Size (area t)
biggestTriangle (Primitive (Rectangle x y)) =
  NoTriangle
biggestTriangle (Primitive (Circle x)) =
  NoTriangle
biggestTriangle (Combine pic pic1) =
  let t1 = biggestTriangle pic in
  let t2 = biggestTriangle pic1 in
  biggestArea t1 t2
biggestTriangle (Rotate x pic) =
  biggestTriangle pic
biggestTriangle (Translate x y pic) =
  biggestTriangle pic

data DivResult = DivByZero | Result Double

safeDivide : Double -> Double -> DivResult
safeDivide x y =
  if y == 0 then DivByZero else Result (x / y)

data Tree a
  = Empty
  | Node (Tree a) a (Tree a)

%name Tree tree, tree1

insert : Ord a => a -> Tree a -> Tree a
insert x Empty =
  Node Empty x Empty
insert x t@(Node left y right) =
  case compare x y of
    LT => Node (insert x left) y right
    EQ => t
    GT => Node left y (insert x right)

listToTree : Ord a => List a -> Tree a
listToTree [] = Empty
listToTree (x :: xs) =
  insert x (listToTree xs)

treeToList : Tree a -> List a
treeToList Empty =
  []
treeToList (Node left x right) =
  treeToList left ++ [x] ++ treeToList right

data Expr
  = Val Int
  | Add Expr Expr
  | Sub Expr Expr
  | Mul Expr Expr

evaluate : Expr -> Int
evaluate (Val x) = x
evaluate (Add x y) = evaluate x + evaluate y
evaluate (Sub x y) = evaluate x - evaluate y
evaluate (Mul x y) = evaluate x * evaluate y

maxMaybe : Ord a => Maybe a -> Maybe a -> Maybe a
maxMaybe Nothing m = m
maxMaybe m Nothing = m
maxMaybe m1@(Just x) m2@(Just y) =
  if x > y then m1 else m2

data PowerSource
  = Petrol
  | Pedal
  | Electric

data Vehicle : PowerSource -> Type where
  Bicycle : Vehicle Pedal
  Car : (fuel : Nat) -> Vehicle Petrol
  Bus : (fuel : Nat) -> Vehicle Petrol
  Unicycle : Vehicle Pedal
  Motorcycle : (fuel : Nat) -> Vehicle Petrol
  Tram : Vehicle Electric

wheels : Vehicle power -> Nat
wheels Bicycle = 2
wheels Tram = 12
wheels (Car _) = 4
wheels (Bus _) = 4
wheels Unicycle = 1
wheels (Motorcycle _) = 2

refuel : Vehicle Petrol -> Vehicle Petrol
refuel (Car _) = Car 100
refuel (Motorcycle _) = Motorcycle 50
refuel (Bus _) = Bus 200

elType : List a -> Type
elType _ = a

data Vect : Nat -> Type -> Type where
  Nil : Vect 0 a
  (::) : (x : a) -> (xs : Vect n a) -> Vect (S n) a

%name Vect xs, ys, zs

append : Vect n a -> Vect m a -> Vect (n + m) a
append [] ys = ys
append (x :: xs) ys = x :: append xs ys

zip : Vect n a -> Vect n b -> Vect n (a, b)
zip [] _ = []
zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys

impL : Vect n a -> Nat
impL {n} _ = n

vectTake : (m : Fin n) -> Vect n a -> Vect (finToNat m) a
vectTake FZ _ = []
vectTake (FS i) (x :: xs) = x :: vectTake i xs
