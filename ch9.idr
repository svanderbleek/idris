module Ch9

import Data.Vect

removeElem : DecEq a
  => (e : a)
  -> (v : Vect (S n) a)
  -> (p : Elem e v)
  -> Vect n a
removeElem e (e :: xs) Here = xs
removeElem {n = S k} e (x :: xs) (There later) =
  x :: removeElem e xs later
removeElem {n = Z} _ (_ :: []) (There Here) impossible
removeElem {n = Z} _ (_ :: []) (There (There _)) impossible

removeElem_auto : DecEq a
  => (e : a)
  -> (v : Vect (S n) a)
  -> {auto p : Elem e v}
  -> Vect n a
removeElem_auto e v {p} = removeElem e v p

maryInVector : Elem "Mary" ["Peter", "Paul", "Mary"]
maryInVector = There (There Here)

