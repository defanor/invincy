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

Perhaps more elaborate (and handy) alternatives will be added in the
future.


## ToDo ##

As mentioned above, invertible alternatives can use some refinement;
lists should be replaced with generic streams; perhaps some state
should be added; error reporting should be improved;
documentation/comments should be written.


## Examples ##

`Json.idr` contains a half-baked JSON implementation for testing.

### Invertible ###

Here is how printers and parsers can be defined simultaneously:

```idris
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
```

### Incremental ###

The JSON example's `main` function:

```idris
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
```

`parseWith'` is what reads data (one line at a time, with the provided
function) and feeds it to the parser, which parses it
incrementally. The result:

```
Type some JSON here:
{
  "foo": [1,2],
  "bar":  3
 , "baz": {"
something \" else"
  :
 [ ]
  }
 ,"last" :
42}
Parsed! Printing:
{ "bar" : 3 , "baz" : { "\nsomething \" else" : [  ] } , "foo" : [ 1 , 2 ] , "last" : 42 }
```
