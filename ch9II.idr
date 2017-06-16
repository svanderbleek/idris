module Ch9II

data Vect : (k : Nat) -> (a : Type) -> Type where
  Nil : Vect 0 a
  (::) : (x : a) -> (xs : Vect n a) -> Vect (S n) a

data Elem : a -> Vect k a -> Type where
  Here : Elem x (x :: xs)
  There : (later : Elem x xs) -> Elem x (y :: xs)

notInNil : Elem e [] -> Void
notInNil Here impossible
notInNil (There _) impossible

notInTail
  :  (notHere : (e = x) -> Void)
  -> (notThere : Elem e xs -> Void)
  -> Elem e (x :: xs) -> Void
notInTail notHere notThere Here = notHere Refl
notInTail notHere notThere (There later) = notThere later

isElem : DecEq a => (e : a) -> (v : Vect n a) -> Dec (Elem e v)
isElem e [] = No notInNil
isElem e (x :: xs) =
  case decEq e x of
    Yes Refl => Yes Here
    No notHere =>
      case isElem e xs of
        Yes prf => Yes (There prf)
        No notThere => No (notInTail notHere notThere)

data ElemList : a -> List a -> Type where
  HereList : ElemList x (x :: xs)
  ThereList : (later : ElemList x xs) -> ElemList x (y :: xs)

data Last : List a -> a -> Type where
  LastOne : Last [value] value
  LastCons : (prf : Last xs value) -> Last (x :: xs) value

last123 : Last [1,2,3] 3
last123 = LastCons (LastCons LastOne)

Uninhabited (Last [] x) where
  uninhabited Void impossible

singleNotLast : (notEql : (x = value) -> Void) -> Last [x] value -> Void
singleNotLast notEql LastOne = notEql Refl
singleNotLast _ (LastCons LastOne) impossible
singleNotLast _ (LastCons (LastCons _)) impossible

emptyNotLast : Last [] value -> Void
emptyNotLast LastOne impossible
emptyNotLast (LastCons _) impossible

notLastStep : (notLast : Last (y :: xs) value -> Void) -> Last (x :: (y :: xs)) value -> Void
notLastStep notLast (LastCons prf) = notLast prf

isLast : DecEq a => (xs : List a) -> (value : a) -> Dec (Last xs value)
isLast [] value = No emptyNotLast
isLast [x] value =
  case decEq x value of
    Yes Refl => Yes LastOne
    No notEql => No $ (singleNotLast notEql)
isLast (x :: y :: xs) value =
  case isLast (y :: xs) value of
    Yes prf => Yes (LastCons prf)
    No notLast => No $ notLastStep notLast
