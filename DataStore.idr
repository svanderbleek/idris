module Main

import Data.Vect

data DataStore : Type where
  MkData : (size : Nat)
         -> (items : Vect size String)
         -> DataStore

size : DataStore -> Nat
size (MkData size' _) = size'

items: (store : DataStore) -> Vect (size store) String
items (MkData _ items') = items'

addToStore : DataStore -> String -> DataStore
addToStore (MkData _ items) item =
  MkData _ (addToEnd items)
  where
    addToEnd : Vect n String -> Vect (S n) String
    addToEnd [] = [item]
    addToEnd (x :: xs) = x :: addToEnd xs

data Command
  = Add String
  | Get Integer
  | Quit
  | Size
  | Search String

parseCommand : (cmd : String) -> (args : String) -> Maybe Command
parseCommand "add" str = Just (Add str)
parseCommand "search" str = Just (Search str)
parseCommand "size" _ = Just Size
parseCommand "get" int =
  case all isDigit (unpack int) of
    False => Nothing
    True => Just (Get (cast int))
parseCommand "quit" _ = Just Quit
parseCommand _ _ = Nothing

parse : (input : String) -> Maybe Command
parse input =
  case span (/= ' ') input of
    (cmd, args) => parseCommand cmd (ltrim args)

getCommand : (store : DataStore) -> (id : Integer) -> (String, DataStore)
getCommand store id =
  case integerToFin id (size store) of
    Nothing => ("Out of Range\n", store)
    (Just id) => (index id (items store) ++ "\n", store)

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
