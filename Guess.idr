module Main

import System

readNumber : IO (Maybe Nat)
readNumber =
  do
    input <- getLine
    pure $ if all isDigit (unpack input)
      then Just (cast input)
      else Nothing

guess : (a : Nat) -> IO ()
guess a =
  do
    putStr "Guess: "
    (Just g) <- readNumber
    | Nothing => guess a
    if g == a
    then
      putStr "You win!"
    else
      do
        putStrLn "Nope"
        guess a

main : IO ()
main =
  do
    r <- time
    guess . cast $ mod r 2
