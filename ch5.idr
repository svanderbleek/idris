module Ch5

import Data.Vect

printLength : IO ()
printLength =
  getLine >>= putStrLn . show . length

printLonger : IO ()
printLonger =
  do
    s1 <- length <$> getLine
    s2 <- length <$> getLine
    putStrLn (show (max s1 s2))

printLonger' : IO ()
printLonger' =
  getLine >>= \s1 =>
  getLine >>= \s2 =>
  putStrLn (show (maxS s1 s2))
  where
    maxS : String -> String -> Nat
    maxS s1 s2 = max (length s1) (length s2)

readNumber : IO (Maybe Nat)
readNumber =
  do
    input <- getLine
    if all isDigit (unpack input)
      then pure (Just (cast input))
      else pure Nothing

readPair : IO (String, String)
readPair =
  do
    s1 <- getLine
    s2 <- getLine
    pure (s1, s2)

usePair : IO ()
usePair =
  do
    (s1, s2) <- readPair
    putStrLn ("You entered " ++ s1 ++ " and " ++ s2)

readNumbers : IO (Maybe (Nat, Nat))
readNumbers =
  do
    Just n1 <- readNumber | Nothing => pure Nothing
    Just n2 <- readNumber | Nothing => pure Nothing
    pure (Just (n1, n2))

repl' : String -> (String -> String) -> IO ()
repl' prompt step = do
  putStrLn prompt
  input <- getLine
  putStrLn $ step input
  repl' prompt step

replWith' : a -> String -> (a -> String -> Maybe (String, a)) -> IO ()
replWith' state prompt step = do
  putStrLn prompt
  input <- getLine
  case step state input of
    Nothing => pure ()
    Just (output, state') => do
      putStrLn output
      replWith' state' prompt step

readVectLen : (len : Nat) -> IO (Vect len String)
readVectLen Z = pure []
readVectLen (S k) = do
  x <- getLine
  xs <- readVectLen k
  pure $ x :: xs

data VectUnknown : Type -> Type where
  MkVect : (len : Nat) -> Vect len a -> VectUnknown a

readVect : IO (VectUnknown String)
readVect = do
  x <- getLine
  if x == "" then
    pure (MkVect _ [])
  else do
    MkVect _ xs <- readVect
    pure $ MkVect _ (x::xs)

printVect : Show a => VectUnknown a -> IO ()
printVect (MkVect len xs) =
  putStrLn (show xs ++ " (length " ++ show len ++ ")")
