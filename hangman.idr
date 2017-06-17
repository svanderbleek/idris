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

nilNotValidInput : ValidInput [] -> Void
nilNotValidInput (Letter _) impossible

manyNotValidInput : ValidInput (x :: (y :: xs)) -> Void
manyNotValidInput (Letter _) impossible

isValidInput : (cs : List Char) -> Dec (ValidInput cs)
isValidInput [] = No nilNotValidInput
isValidInput (x :: []) = Yes (Letter x)
isValidInput (x :: (y :: xs)) = No manyNotValidInput

readGuess : IO (x ** ValidInput x) readGuess = do
  guess <- unpack . toUpper <$> getLine
  case isValidInput guess of
    Yes prf => pure (guess ** prf)
    No contra => readGuess

removeElem :
  DecEq a =>
  (e : a) ->
  (v : Vect (S n) a) ->
  (p : Elem e v) ->
  Vect n a
removeElem {n = Z} _ (_ :: []) (There Here) impossible
removeElem {n = Z} _ (_ :: []) (There (There _)) impossible
removeElem e (e :: xs) Here = xs
removeElem {n = S k} e (x :: xs) (There later) =
  x :: removeElem e xs later

processGuess :
  (guess : Char) ->
  (WordState (S guesses) (S letters)) ->
  Either (WordState guesses (S letters)) (WordState (S guesses) letters)
processGuess guess (MkWordState word missing) =
  case isElem guess missing of
    Yes prf => Right (MkWordState word (removeElem guess missing prf))
    No contra => Left (MkWordState word missing)

game : WordState (S guesses) (S letters) -> IO Finished
game (MkWordState w xs) = do
  ?q
