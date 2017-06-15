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
  -> Elem e (x :: xs)
notInTail notHere notThere = ?notInTail_rhs_2

isElem : DecEq a => (e : a) -> (v : Vect n a) -> Dec (Elem e v)
isElem e [] = No notInNil
isElem e (x :: xs) =
  case decEq e x of
    Yes Refl => Yes Here
    No notHere =>
      case isElem e xs of
        Yes prf => Yes (There prf)
        No notThere => No $ notInTail notHere notThere
