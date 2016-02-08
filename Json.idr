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

data JsonType = JTString
              | JTNumber
              | JTBool
              | JTNull
              | JTArray
              | JTObject

implementation DecEq JsonType where
  decEq JTString JTString = Yes Refl
  decEq JTNumber JTNumber = Yes Refl
  decEq JTBool JTBool = Yes Refl
  decEq JTNull JTNull = Yes Refl
  decEq JTArray JTArray = Yes Refl
  decEq JTObject JTObject = Yes Refl
  decEq x y = No $ believe_me (x = y -> Void) -- won't need those

jcArgs : JsonType -> Type
jcArgs JTString = String
jcArgs JTNumber = Double
jcArgs JTBool = Bool
jcArgs JTNull = ()
jcArgs JTArray = List JsonValue
jcArgs JTObject = SortedMap String JsonValue

dsJson : JsonValue -> (x ** jcArgs x)
dsJson (JsonString s) = (JTString ** s)
dsJson (JsonNumber n) = (JTNumber ** n)
dsJson (JsonBool b) = (JTBool ** b)
dsJson JsonNull = (JTNull ** ())
dsJson (JsonArray a) = (JTArray ** a)
dsJson (JsonObject o) = (JTObject ** o)



jsonNull' : PP (List Char) ()
jsonNull' = list' $ unpack "null"

jsonBool' : PP (List Char) Bool
jsonBool' = choices' {f=const ()} {e=Bool} (const {b=()}) (\b => (b ** ()))
  [(True ** list' (unpack "true")),
   (False ** list' (unpack "false"))]

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
  jsonValue' : PP (List Char) JsonValue
  jsonValue' = choices dsJson
    [ (JTString ** (JsonString, jsonString'))
    , (JTNumber ** (JsonNumber, jsonNumber'))
    , (JTBool ** (JsonBool, jsonBool'))
    , (JTNull ** (const JsonNull, jsonNull'))
    , (JTArray ** (JsonArray, jsonArray'))
    , (JTObject ** (JsonObject, jsonObject'))
    ]

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
json' = choices dsJson
  [ (JTArray ** (JsonArray, jsonArray'))
  , (JTObject ** (JsonObject, jsonObject'))
  ]

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
