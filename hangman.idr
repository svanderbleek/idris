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
  Default : (game : WordState 0 0) -> Finished

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

readGuess : IO (c ** ValidInput c)
readGuess = do
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

isFinished : (state : WordState guesses letters) -> Dec Finished
isFinished {guesses = Z} {letters = Z} state = Yes $ Default state
isFinished {guesses = Z} {letters = (S k)} state = Yes (Lost state)
isFinished {guesses = (S k)} {letters = Z} state = Yes (Won state)
isFinished {guesses = (S k)} {letters = (S j)} state = No ?notFinished

checkFinished :
  Either (WordState guesses (S letters)) (WordState (S guesses) letters) ->
  Dec Finished
checkFinished (Left l) = isFinished l
checkFinished (Right r) = isFinished r

game : WordState (S guesses) (S letters) -> IO Finished
game state = do
  (_ ** Letter guess) <- readGuess
  let nextState = processGuess guess state
  case checkFinished nextState of
    Yes prf => pure prf
    No contra => game $ fromEither nextState
