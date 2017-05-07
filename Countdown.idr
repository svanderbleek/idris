module Main

import System

countdown : (secs : Nat) -> IO ()
countdown Z = putStrLn "Blast off!"
countdown s@(S n) =
  do
    putStrLn (show s)
    usleep 1000000
    countdown n

readNumber : IO (Maybe Nat)
readNumber =
  do
    n <- getLine
    if all isDigit (unpack n)
      then pure . Just $ cast n
      else pure Nothing

countdowns : IO ()
countdowns =
  do
    putStr "Enter starting number: "
    Just s <- readNumber
    | Nothing =>
      do
        putStrLn "Invalid input"
        countdowns
    countdown s
    putStr "Another (y/n)? "
    a <- getLine
    if a == "y"
      then countdowns
      else pure ()
