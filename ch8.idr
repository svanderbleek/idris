module Ch8

data Vect : Nat -> Type -> Type where
  Nil : Vect Z a
  (::) : a -> Vect k a -> Vect (S k) a

data EqNat : (n1 : Nat) -> (n2 : Nat) -> Type where
  Same : (n : Nat) -> EqNat n n

sameS : (eq : EqNat k j) -> EqNat (S k) (S j)
sameS (Same k) = Same (S k)

checkEqNat : (n1 : Nat) -> (n2 : Nat) -> Maybe (EqNat n1 n2)
checkEqNat Z Z = Just (Same 0)
checkEqNat Z (S k) = Nothing
checkEqNat (S k) Z = Nothing
checkEqNat (S k) (S j) = do
  eq <- checkEqNat k j
  pure (sameS eq)

exactLength : (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
exactLength {m} len input = do
  (Same len) <- checkEqNat len m
  pure input

same_cons
  : {xs : List a}
  -> {ys : List a}
  -> xs = ys
  -> x :: xs = x :: ys
same_cons prf = cong prf


same_lists
  : {xs : List a}
  -> {ys : List a}
  -> x = y
  -> xs = ys
  -> x :: xs = x :: ys
same_lists _ pxs = cong pxs

data ThreeEq : a -> b -> c -> Type where
  SameThree : (x : a) -> ThreeEq x x x

allSameS : (x, y, z : Nat) -> ThreeEq x y z -> ThreeEq (S x) (S y) (S z)
allSameS z z z (SameThree z) = SameThree (S z)
