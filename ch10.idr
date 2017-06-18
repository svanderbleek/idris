module Ch10

data ListLast : List a -> Type where
  Empty : ListLast []
  NonEmpty : (xs : List a) -> (x : a) -> ListLast (xs ++ [x])

describeHelper : (input : List Int) -> (form : ListLast input) -> String
describeHelper [] Empty = "Empty"
describeHelper (xs ++ [x]) (NonEmpty xs x) = "Nonempty, initial = " ++ show (xs)

listLast : (xs : List a) -> ListLast xs
listLast [] = Empty
listLast (x :: xs) =
  case listLast xs of
    Empty => NonEmpty [] x
    NonEmpty xs x => ?y_3

describeListEnd : List Int -> String
describeListEnd [] = ?describeListEnd_rhs_1
-- describeListEnd (xs ++ [x]) = ?describeListEnd_rhs_2
