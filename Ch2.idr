module Ch2

palindrome : String -> Bool
palindrome s =
  s == reverse s

palindrome' : String -> Bool
palindrome' =
  palindrome . toLower

palindrome'' : Nat -> String -> Bool
palindrome'' n s =
  if length s > n then palindrome' s else False

counts : String -> (Nat, Nat)
counts s =
  let ws = words s in
  (length ws, length s)

top_ten : Ord a => List a -> List a
top_ten l =
  take 10 (sort l)

over_length : Nat -> List String -> Nat
over_length n =
  length . (filter ((>n) . length))
