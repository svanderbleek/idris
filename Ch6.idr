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
  | Dub Format
  | Chr Format
  | Str Format
  | Lit String Format
  | End

PrintfType : Format -> Type
PrintfType (Number x) = (i : Int) -> PrintfType x
PrintfType (Dub x) = (d : Double) -> PrintfType x
PrintfType (Chr x) = (c : Char) -> PrintfType x
PrintfType (Str x) = (s : String) -> PrintfType x
PrintfType (Lit x y) = PrintfType y
PrintfType End = String

printfFmt : (fmt : Format) -> (acc : String) -> PrintfType fmt
printfFmt (Number fmt) acc = \i => printfFmt fmt (acc ++ show i)
printfFmt (Dub fmt) acc = \d => printfFmt fmt (acc ++ show d)
printfFmt (Chr fmt) acc = \c => printfFmt fmt (acc ++ cast c)
printfFmt (Str fmt) acc = \s => printfFmt fmt (acc ++ s)
printfFmt (Lit lit fmt) acc = printfFmt fmt (acc ++ lit)
printfFmt End acc = acc

toFormat : (xs : List Char) -> Format
toFormat [] = End
toFormat ('%' :: 'd' :: xs) = Number (toFormat xs)
toFormat ('%' :: 'f' :: xs) = Dub (toFormat xs)
toFormat ('%' :: 'c' :: xs) = Chr (toFormat xs)
toFormat ('%' :: 's' :: xs) = Str (toFormat xs)
toFormat ('%' :: xs) = Lit "%" (toFormat xs)
toFormat (x :: xs) =
  case toFormat xs of
    Lit lit xs' => Lit (strCons x lit) xs'
    fmt => Lit (strCons x "") fmt

printf : (fmt : String) -> PrintfType (toFormat (unpack fmt))
printf fmt = printfFmt _ ""

Matrix : Nat -> Nat -> Type
Matrix k j = Vect k (Vect j Double)

testMatrix : Matrix 2 3
testMatrix =
  [[0,0,0]
  ,[0,0,0]]

TupleVect : (n : Nat) -> (t : Type) -> Type
TupleVect Z _ = ()
TupleVect (S k) t = (t, TupleVect k t)

testTupleVect : TupleVect 4 Nat
testTupleVect = (0, 0, 0, 0, ())
