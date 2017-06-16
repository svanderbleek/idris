module Hangman

import Data.Vect

data WordState : (guesses : Nat) -> (letters : Nat) -> Type where
  MkWordState
    :  (word : String)
    -> (missing : Vect letters Char)
    -> WordState guesses letters

data Finished : Type where
  Lost : (game : WordState 0 (S letters)) -> Finished
  Won : (game : WordState (S guesses) 0) -> Finished

data ValidInput : List Char -> Type where
  Letter : (c : Char) -> ValidInput [c]

Uninhabited (ValidInput []) where
  uninhabited (Letter _) impossible

isValidInput : (cs : List Char) -> Dec (ValidInput cs)
isValidInput [] = No $ uninhabited
isValidInput (x :: []) = Yes (Letter x)
isValidInput (x :: (y :: xs)) = ?isValidInput_rhs_4

isValidString : (s : String) -> Dec (ValidInput (unpack s))
isValidString s = ?isValidString_rhs

readGuess : IO (x ** ValidInput x)
readGuess = ?readGuess_rhs

game : WordState (S guesses) (S letters) -> IO Finished
game (MkWordState w xs) = do
  next <- getLine
  ?q
