module Ch6

import Data.Vect

%default total

Position : Type
Position =
  (Double, Double)

Polygon : Nat -> Type
Polygon n =
  Vect n Position

tri : Polygon 3
tri =
  [(0.0, 0.0)
  ,(0.0, 0.0)
  ,(0.0, 0.0)]

StringOrInt : Bool -> Type
StringOrInt False = String
StringOrInt True = Int

getStringOrInt : (isInt : Bool) -> StringOrInt isInt
getStringOrInt False = "Ninety Four"
getStringOrInt True = 94

valToString : (isInt : Bool) -> StringOrInt isInt -> String
valToString False x = trim x
valToString True x = cast x
