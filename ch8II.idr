module Ch8II

import Data.Vect

reverse' : Vect n a -> Vect n a
reverse' [] = []
reverse' (x :: xs) =
  reverseProof (reverse' xs ++ [x])
  where
    reverseProof : Vect (k + 1) a -> Vect (S k) a
    reverseProof {k} term = rewrite plusCommutative 1 k in term
