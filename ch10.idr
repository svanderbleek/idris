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
    NonEmpty ys y => NonEmpty (x :: ys) y

describeListEnd : List Int -> String
describeListEnd xs with (listLast xs)
  describeListEnd [] | Empty = "empty"
  describeListEnd (ys ++ [x]) | (NonEmpty ys x) = "nonempty, initial = " ++ show ys

myReverse : List a -> List a
myReverse xs with (listLast xs)
  myReverse [] | Empty = []
  myReverse (ys ++ [x]) | (NonEmpty ys x) = x :: myReverse ys

data SplitList : List a -> Type where
  SplitNil : SplitList []
  SplitOne : (x : a) -> SplitList [x]
  SplitPair : (left : List a) -> (right : List a) -> SplitList (left ++ right)

splitListDup : (xs : List a) -> (xs : List a) -> SplitList xs
splitListDup xs ys = ?splitListInTwo_rhs

splitList : (xs : List a) -> SplitList xs
splitList xs = splitListDup xs xs

mergeSort : Ord a => List a -> List a
mergeSort xs with (splitList xs)
  mergeSort [] | SplitNil = []
  mergeSort [x] | (SplitOne x) = [x]
  mergeSort (left ++ right) | (SplitPair left right) = merge (mergeSort right) (mergeSort left)
