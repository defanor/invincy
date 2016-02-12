# Invincy #

Invertible and incremental parser combinator library.


## Description ##

Incremental parsing is just hacked together: continuations are
returned when there is not enough input.

Invertible parts are implemented on top of regular incremental ones,
so they are not enforced. To be precise, printers are implemented
separately, and then they are joined together. The approach is similar
to that from "invertible syntax descriptions", but without
per-constructor or failing printers, and with regular tuples instead
of syntax classes: the first element is a parser (covariant), the
second is a printer (contravariant). Therefore the printing
combinators can't be monadic, while the parsing ones can.


### Alternatives ###

Invertible alternatives are rather tricky: since the printers
shouldn't fail, and there is no per-constructor printers here (since
it's also awkward to make printers that should fail on each
constructor except for one, unless it is done automatically, using
metaprogramming), the primary alternative selection accepts just one
printer, but multiple parsers:

```idris
(<||>) : LazyAlternative f => {g: Type -> Type} -> (f a, g a) -> Lazy (f a) -> (f a, g a)
(<||>) (fa, ga) fb = (fa <|> fb, ga)
```

Yet there is a couple of other options, making use of `Decidable`
(contravariant alternative):

```idris
either' : (Functor f, LazyAlternative f, Decidable g) =>
  (f a, g a) -> (f b, g b) -> (f (Either a b), g (Either a b))
either' (fa, ga) (fb, gb) = (map Left fa <|> map Right fb, chosen ga gb)

choice' : (Functor f, LazyAlternative f, Decidable g) =>
  (a -> Either a a) -> (f a, g a) -> (f a, g a) -> (f a, g a)
choice' e (fa, ga) (fb, gb) = (fa <|> fb, choose e ga gb)
```

And a couple of `choices` functions, to generate those choices from
lists:

```idris
choices : DecEq e
   => {f: e -> (a ** a -> t)}
   -> (d: t -> (x: e ** getWitness (f x)))
   -> (l: LazyList (x:e ** PP (List Char) (getWitness (f x))))
   -> PP (List Char) t
```

But those require some boilerplate code, which may be generated
automatically if it'll come to metaprogramming.


## Examples ##

`Json.idr` contains a half-baked JSON implementation for testing.

### Invertible ###

Here is how printers and parsers can be defined simultaneously:

```idris
mutual
  jsonValue' : PP (List Char) JsonValue
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
    sepBy' jsonValue'
           (spaces' *> val' ',' <* spaces')
    <* spaces' <* val' ']'

  jsonObject' : PP String (SortedMap String JsonValue)
  jsonObject' = (fromList, toList) <$>
    (val' '{' *> spaces' *>
     sepBy' (jsonString' <* spaces' <* val' ':' <* spaces' <*> jsonValue')
            (spaces' *> val' ',' <* spaces')
     <* spaces' <* val' '}')
```

### Incremental ###

The JSON example's `main` function:

```idris
main : IO ()
main = do
  putStrLn "Type some JSON here:"
  v <- parseWith' (spaces' **> json') (((++) "\n") <$> getLine)
  case v of
    Done i x => do
      putStrLn "Parsed! Printing:"
      putStrLn $ print' json' x
    Failure s => putStrLn $ "Failure: " ++ s
    Partial _ => putStrLn "Uh oh, partial"
  main
```

`parseWith'` is what reads data (one line at a time, with the provided
function) and feeds it to the parser, which parses it
incrementally. The result:

```
Type some JSON here:
{
  "foo" : "bar",
  "baz": 3
 ,"qux" :3.42 ,
       "str"  : "string \" here",
 "arr": [1, 2.3, "4", [], {}],
"obj":{"a":0},
"last":{}}
Parsed! Printing:
{ "arr" : [ 1 , 2.3 , "4" , [  ] , {  } ] , "baz" : 3 , "foo" : "bar" , "last" : {  } , "obj" : { "a" : 0 } , "qux" : 3.42 , "str" : "string \" here" }
Type some JSON here:
{ "arr" : [ 1 , 2.3 , "4" , [  ] , {  } ] , "baz" : 3 , "foo" : "bar" , "last" : {  } , "obj" : { "a" : 0 } , "qux" : 3.42 , "str" : "string \" here" }
Parsed! Printing:
{ "arr" : [ 1 , 2.3 , "4" , [  ] , {  } ] , "baz" : 3 , "foo" : "bar" , "last" : {  } , "obj" : { "a" : 0 } , "qux" : 3.42 , "str" : "string \" here" }
```
