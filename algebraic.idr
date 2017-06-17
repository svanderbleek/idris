module algebraicwith

data Bit = O | I

or : Bit -> Bit -> Bit
or O b = b
or I _ = I

orAssociative : (a : Bit) -> (b : Bit) -> (c : Bit) -> (a `or` b) `or` c = a `or` (b `or` c)
orAssociative O b c = Refl
orAssociative I b c = Refl

BitString : Type
BitString = List Bit

bsor : BitString -> BitString -> BitString
bsor [] ys = ys
bsor xs [] = xs
bsor (x :: xs) (y :: ys) = or x y :: bsor xs ys

bsorAssociative :
  (as : BitString) ->
  (bs : BitString) ->
  (cs : BitString) ->
  (as `bsor` bs) `bsor` cs = as `bsor` (bs `bsor` cs)
bsorAssociative [] bs cs = Refl
bsorAssociative (x :: xs) [] cs = Refl
bsorAssociative (x :: xs) (y :: ys) [] = Refl
bsorAssociative (x :: xs) (y :: ys) (z :: zs) =
  rewrite orAssociative x y z in
  rewrite bsorAssociative xs ys zs in
  Refl
