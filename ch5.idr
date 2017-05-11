module Ch5

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
