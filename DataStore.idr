module Main

import Data.Vect

infixr 5 .+.

data Schema
  = SStr
  | SInt
  | (.+.) Schema Schema

SchemaType : Schema -> Type
SchemaType SStr = String
SchemaType SInt = Int
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

record DataStore where
  constructor MkData
  schema : Schema
  size : Nat
  items : Vect size (SchemaType schema)

addToStore : (store : DataStore) -> (SchemaType (schema store)) -> DataStore
addToStore (MkData schema _ items) item =
  MkData _ _ (addToEnd items)
  where
    addToEnd : Vect n (SchemaType schema) -> Vect (S n) (SchemaType schema)
    addToEnd [] = [item]
    addToEnd (x :: xs) = x :: addToEnd xs

data Command : Schema -> Type where
  Add : SchemaType schema -> Command schema
  Get : Integer -> Command schema
  Quit : Command schema
  Size : Command schema
  Search : String -> Command schema

parseCommand : (schema : Schema) -> (cmd : String) -> (args : String) -> Maybe (Command schema)
parseCommand schema "add" str = Just (Add (?parseschema str))
parseCommand schema "search" str = Just (Search str)
parseCommand schema "size" _ = Just Size
parseCommand schema "get" int =
  case all isDigit (unpack int) of
    False => Nothing
    True => Just (Get (cast int))
parseCommand schema "quit" _ = Just Quit
parseCommand _ _ _ = Nothing

parse : (schema : Schema) -> (input : String) -> Maybe (Command schema)
parse schema input =
  case span (/= ' ') input of
    (cmd, args) => parseCommand schema cmd (ltrim args)

{-
getCommand : (store : DataStore) -> (id : Integer) -> (String, DataStore)
getCommand store id =
  case integerToFin id (size store) of
    Nothing => ("Out of Range\n", store)
    (Just id) => (?showa (index id (items store)) ++ "\n", store)

-- Wrong Index tracking but meh
searchCommand : (items : Vect n String) -> (q : String) -> (found : List String) -> String
searchCommand [] _ found =
  if length found > 0 then
    (foldr1 (\next, out => out ++ ", " ++ next) found) ++ "\n"
  else
    "No entries found\n"
searchCommand (item :: items) q found =
  if isInfixOf q item then
    searchCommand items q (((show (length items)) ++ ": " ++ item) :: found)
  else
    searchCommand items q found

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store input =
  case parse input of
    Nothing => Just ("Invalid command\n", store)
    (Just (Add item)) =>
      Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
    (Just (Get id)) => Just (getCommand store id)
    (Just Size) => Just (show (size store) ++ " entries in store\n", store)
    (Just (Search q)) => Just (searchCommand (items store) q [], store)
    (Just Quit) => Nothing

main : IO ()
main =
  replWith (MkData _ []) "Command: " processInput
-}
