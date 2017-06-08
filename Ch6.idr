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

valToString' : (isInt : Bool) -> (case isInt of
                                       False => String
                                       True => Int) -> String
valToString' False x = trim x
valToString' True x = cast x 


AdderType : (numargs : Nat) -> Type -> Type
AdderType Z numType = numType
AdderType (S k) numType = (next : numType) -> AdderType k numType

adder : Num numType => (numargs : Nat) -> (acc : numType) -> AdderType numargs numType
adder Z acc = acc
adder (S k) acc = \next => adder k (next + acc)

data Format
  = Number Format
  | Str Format
  | Lit String Format
  | End

PrintfType : Format -> Type
PrintfType (Number x) = (i : Int) -> PrintfType x
PrintfType (Str x) = (s : String) -> PrintfType x
PrintfType (Lit x y) = PrintfType y
PrintfType End = String

printfFmt : (fmt : Format) -> (acc : String) -> PrintfType fmt
printfFmt fmt acc = ?printfFmt_rhs
