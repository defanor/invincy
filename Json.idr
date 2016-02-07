module Main

import Invincy.Parsing
import Invincy.Printing
import Invincy.Invertible

import Data.SortedMap

data JsonValue = JsonString String
               | JsonNumber Double
               | JsonBool Bool
               | JsonNull
               | JsonArray (List JsonValue)
               | JsonObject (SortedMap String JsonValue)

jsonNull' : PP (List Char) ()
jsonNull' = list' $ unpack "null"

jsonBool' : PP (List Char) Bool
jsonBool' = choice' eitherBool 
                    ((const False, const ()) <$$> list' (unpack "false"))
                    ((const True, const ()) <$$> list' (unpack "true"))
  where
    eitherBool : Bool -> Either Bool Bool
    eitherBool False = Left False
    eitherBool True = Right True

jsonNumber : Parser (List Char) Double
jsonNumber = do
  x <- getWitness <$> some digit
  y <- option $ Prelude.Applicative.(*>) (val '.') (getWitness <$> some digit)
  return $ cast . pack $ x ++ (maybe neutral ('.' ::) y)

jsonNumber' : PP (List Char) Double
jsonNumber' = (jsonNumber, MkPrinter $ unpack . show)

jsonString : Parser (List Char) String
jsonString = val '"' *> (pack <$> jsonStr)
  where
    jsonStr : Parser (List Char) (List Char)
    jsonStr = (val '"' *> pure []) <|> do
      c <- sat (/= '"')
      if (c == '\\')
      then (::) <$> oneOf ['"', '\\', '/', '\b', '\f', '\n', '\r', '\t'] <*> jsonStr
      else (c ::) <$> jsonStr

jsonString' : PP (List Char) String
jsonString' = (jsonString, MkPrinter $ unpack . show)

mutual
  jsonValP : JsonValue -> List Char
  jsonValP (JsonString s) = print' jsonString' s
  jsonValP (JsonNumber n) = print' jsonNumber' n
  jsonValP (JsonBool b) = print' jsonBool' b
  jsonValP JsonNull = print' jsonNull' ()
  jsonValP (JsonArray a) = print' jsonArray' a
  jsonValP (JsonObject o) = print' jsonObject' o
  
  jsonValue' : PP (List Char) JsonValue
  jsonValue' = (fst jsonNull' *> pure JsonNull, MkPrinter jsonValP)
          <||> (JsonBool <$> fst jsonBool')
          <||> (JsonNumber <$> jsonNumber)
          <||> (JsonString <$> jsonString)
          <||> (JsonArray <$> fst jsonArray')
          <||> (JsonObject <$> fst jsonObject')
  
  jsonArray' : PP (List Char) (List JsonValue)
  jsonArray' = 
    val' '[' **> spaces' **>
    sepBy' jsonValue'
           (spaces' **> val' ',' <** spaces')
    <** spaces' <** val' ']'

  jsonObject' : PP (List Char) (SortedMap String JsonValue)
  jsonObject' = (fromList, toList) <$$>
    (val' '{' **> spaces' **>
     sepBy' (jsonString' <** spaces' <** (val' ':') <** spaces' <**> jsonValue')
            (spaces' **> val' ',' <** spaces')
     <** spaces' <** val' '}')

json' : PP (List Char) JsonValue
json' = (JsonObject <$> fst jsonObject', MkPrinter jsonValP)
   <||> JsonArray <$> fst jsonArray'

main : IO ()
main = do
  putStrLn "Type some JSON here:"
  v <- parseWith' (spaces' **> json') ((unpack . ((++) "\n")) <$> getLine)
  case v of
    Done i x => do
      putStrLn "Parsed! Printing:"
      putStrLn $ pack $ print' json' x
    Failure s => putStrLn $ "Failure: " ++ s
    Partial _ => putStrLn "Uh oh, partial"
  main
