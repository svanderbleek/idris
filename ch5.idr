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

readVect' : IO (len ** Vect len String)
readVect' = do
  x <- getLine
  if x == "" then
    pure (_ ** [])
  else do
    (_ ** xs) <- readVect'
    pure (_ ** x::xs)

zipIns : IO ()
zipIns = do
  putStrLn "enter v1"
  (l1 ** v1) <- readVect'
  putStrLn "enter v2"
  (l2 ** v2) <- readVect'
  case exactLength l1 v2 of
    Nothing => putStrLn "ya done goofed"
    Just v2' => printLn (zip v1 v2')

readToBlank : IO (List String)
readToBlank = do
  l <- getLine
  if l == "" then
    pure []
  else do
    ls <- readToBlank
    pure $ l :: ls

readAndSave : IO ()
readAndSave = do
  putStrLn "input to write"
  ls <- readToBlank
  putStrLn "file name"
  nm <- getLine
  er <- writeFile nm (show ls)
  case er of
    Right () => putStrLn "ok"
    Left FileError => putStrLn "ok"

readVectf : (f : File) -> IO (n ** Vect n String)
readVectf f = do
  more <- fEOF f
  if not more then do
    Right l <- fGetLine f
    (_ ** ls) <- readVectf f
    pure $ (_ ** l :: ls)
  else
    pure (_ ** [])

readVectFile : (filename : String) -> IO (n ** Vect n String)
readVectFile filename = do
  Right f <- openFile filename Read
  readVectf f



