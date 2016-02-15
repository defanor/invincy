module Main
import Data.SortedMap
import Invincy


data JsonValue = JsonString String
               | JsonNumber Double
               | JsonBool Bool
               | JsonNull
               | JsonArray (List JsonValue)
               | JsonObject (SortedMap String JsonValue)

-- can't generate it with elaborator reflection yet
data JsonType = JTString
              | JTNumber
              | JTBool
              | JTNull
              | JTArray
              | JTObject

-- derivation with Pruviloj.Derive.DecEq leads to strange errors
implementation DecEq JsonType where
  decEq JTString JTString = Yes Refl
  decEq JTNumber JTNumber = Yes Refl
  decEq JTBool JTBool = Yes Refl
  decEq JTNull JTNull = Yes Refl
  decEq JTArray JTArray = Yes Refl
  decEq JTObject JTObject = Yes Refl
  decEq x y = No $ believe_me (x = y -> Void) -- won't need those

jcArgs : JsonType -> (x ** x -> JsonValue)
%runElab (cArgs (NS (UN "jcArgs") ["Main"]))

dsJson : JsonValue -> (x ** getWitness (jcArgs x))
%runElab (dArgs `(\x => getWitness (jcArgs x)) (NS (UN "dsJson") ["Main"]))


jsonNull' : PP String ()
jsonNull' = raw' "null"

jsonBool' : PP String Bool
jsonBool' = choices' {f=const ()} {e=Bool} (const {b=()}) (\b => (b ** ()))
  [(True ** raw' "true"),
   (False ** raw' "false")]

jsonNumber' : PP String Double
jsonNumber' = (jsonNumber, MkPrinter $ fromString . show)
  where
    jsonNumber : Parser String Double
    jsonNumber = do
      x <- getWitness <$> some digit
      y <- option $ Prelude.Applicative.(*>) (val '.') (getWitness <$> some digit)
      return $ cast . pack $ x ++ (maybe neutral ('.' ::) y)

jsonString' : PP String String
jsonString' = (jsonString, MkPrinter $ fromString . show)
  where
    jsonStr : Parser String String
    jsonStr = (val '"' *> pure neutral) <|> do
      c <- sat (/= '"')
      if (c == '\\')
      then cons <$> oneOf ['"', '\\', '/', '\b', '\f', '\n', '\r', '\t'] <*> jsonStr
      else (cons c) <$> jsonStr
    jsonString : Parser String String
    jsonString = val '"' *> jsonStr

mutual
  jsonValue' : PP String JsonValue
  jsonValue' = choices dsJson
    [ (JTString ** jsonString')
    , (JTNumber ** jsonNumber')
    , (JTBool ** jsonBool')
    , (JTNull ** jsonNull')
    , (JTArray ** jsonArray')
    , (JTObject ** jsonObject')
    ]

  jsonArray' : PP String (List JsonValue)
  jsonArray' =
    val' '[' *> spaces' *>
    sepBy' jsonValue' (spaces' *> val' ',' <* spaces')
    <* spaces' <* val' ']'

  jsonObject' : PP String (SortedMap String JsonValue)
  jsonObject' = (fromList, toList) <$>
    (val' '{' *> spaces' *>
     sepBy' (jsonString' <* spaces' <* val' ':' <* spaces' <*> jsonValue')
            (spaces' *> val' ',' <* spaces')
     <* spaces' <* val' '}')

json' : PP String JsonValue
json' = choices dsJson
  [ (JTArray ** jsonArray')
  , (JTObject ** jsonObject')
  ]

main : IO ()
main = do
  putStrLn "Type some JSON here:"
  v <- parseWith' (spaces' *> json') $ (++ "\n") <$> getLine
  case v of
    Done i x => do
      putStrLn "Parsed! Printing:"
      putStrLn $ print' json' x
    Failure s => putStrLn $ "Failure: " ++ s
    Partial _ => putStrLn "Uh oh, partial"
  main
