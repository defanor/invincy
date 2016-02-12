module Invincy.Invertible

import Invincy.Parsing
import Invincy.Printing

%access public export

infixl 4 <$$>
(<$$>) : (Functor f, Contravariant g) => ((a -> b), (b -> a)) -> (f a, g a) -> (f b, g b)
(<$$>) (f', c') (f, c) = (map f' f, contramap c' c)

infixl 2 <**>
(<**>) : (Applicative f, Divisible g) => (f a, g a) -> (f b, g b) -> (f (a, b), g (a, b))
(<**>) (fa, ga) (fb, gb) = (MkPair <$> fa <*> fb, divided ga gb)

infixl 2 <**
(<**) : (Applicative f, Divisible g) => (f a, g a) -> (f b, g ()) -> (f a, g a)
(<**) (fa, ga) (fb, gb) = (fa <* fb, divide (flip MkPair ()) ga gb)

infixl 2 **>
(**>) : (Applicative f, Divisible g) => (f a, g ()) -> (f b, g b) -> (f b, g b)
(**>) (fa, ga) (fb, gb) = (fa *> fb, divide (MkPair ()) ga gb)

infixl 3 <||>
(<||>) : LazyAlternative f => {g: Type -> Type} -> (f a, g a) -> Lazy (f a) -> (f a, g a)
(<||>) (fa, ga) fb = (fa <|> fb, ga)

either' : (Functor f, LazyAlternative f, Decidable g) =>
  (f a, g a) -> (f b, g b) -> (f (Either a b), g (Either a b))
either' (fa, ga) (fb, gb) = (map Left fa <|> map Right fb, chosen ga gb)

choice' : (Functor f, LazyAlternative f, Decidable g) =>
  (a -> Either a a) -> (f a, g a) -> Lazy (f a, g a) -> (f a, g a)
choice' e (fa, ga) b = (fa <|> fst b, choose e ga (snd b))

||| Parser and printer
PP : Type -> Type -> Type
PP a b = (Parser a b, Printer a b)

data LazyList : Type -> Type where
  Nil : LazyList a
  (::) : a -> Lazy (LazyList a) -> LazyList a

||| Generates choices
||| @t data type
||| @e enumeration of constructors
||| @f provides constructor arguments
||| @c constructor
||| @d destructor
||| @l "enumerated" printers/parsers
choices' : (DecEq e, Stream t' s)
   => {f: e -> Type}
   -> (c: (x: e) -> f x -> t)
   -> (d: t -> (x: e ** f x))
   -> (l: LazyList (x:e ** PP s (f x)))
   -> PP s t
choices' dtc dte [] = (fail "Out of alternatives", MkPrinter $ const neutral)
choices' dtc dte ((v ** p)::xs) =
  choice' (\val => let (v' ** p') = dte val in (case decEq v' v of Yes _ => Left; No _ => Right) val)
    ((dtc v, (\val => let (v' ** p') = dte val in (case decEq v' v of Yes eq => replace eq p'))) <$$> p)
    (choices' dtc dte xs)

choices : (DecEq e, Stream t' s)
   => {f: e -> (a ** a -> t)}
   -> (d: t -> (x: e ** getWitness (f x)))
   -> (l: LazyList (x:e ** PP s (getWitness (f x))))
   -> PP s t
choices dte [] = (fail "Out of alternatives", MkPrinter $ const neutral)
choices {f} dte ((v ** p)::xs) =
  choice' (\val => let (v' ** p') = dte val in (case decEq v' v of Yes _ => Left; No _ => Right) val)
    ((getProof (f v),
       (\val => let (v' ** p') = dte val in (case decEq v' v of Yes eq => replace eq p')))
     <$$> p)
    (choices dte xs)



print' : PP i a -> a -> i
print' = runPrinter . snd

parse' : PP i a -> i -> Result i a
parse' = runParser . fst

parseWith' : Monad m => PP i r -> m i -> m (Result i r)
parseWith' = parseWith . fst




||| Parse or print a single item
item' : PP (List a) a
item' = (item, itemP)

||| Parse an item satisfying a predicate, or put any item
sat' : (a -> Bool) -> PP (List a) a
sat' p = (sat p, itemP)

||| Ignore an item on parsing, use a fixed one on printing
ignore' : Stream t s => Parser s a -> s -> PP s ()
ignore' p x = (ignore p, ignoreP x)

||| Parse or print a fixed item
val' : (Eq t, Stream t s) => t -> PP s ()
val' x = (val x, valP x)

||| Just as val, but for multiple tokens
raw' : (Eq t, Stream t s) => s -> PP s ()
raw' l = (raw l, ignoreP l)

||| An optional item
||| @a What to print in case if the value is Nothing
option' : Stream t s => a -> PP s a -> PP s (Maybe a)
option' x (par, pr) = (option par, optionP x pr)

many' : Stream t s => PP s a -> PP s (List a)
many' (par, pr) = (many par, manyP pr)

manyTill' : Stream t s => PP s a -> PP s () -> PP s (List a)
manyTill' (par, pr) (par', pr') = (manyTill par par', manyTillP pr pr')

some' : Stream t s => PP s a -> PP s (x:List a ** NonEmpty x)
some' (par, pr) = (some par, someP pr)

sepBy' : Stream t s => PP s a -> PP s () -> PP s (List a)
sepBy' (par, pr) (par', pr') = (sepBy par par', sepByP pr pr')

sepBy1' : Stream t s => PP s a -> PP s () -> PP s (x:List a ** NonEmpty x)
sepBy1' (par, pr) (par', pr') = (sepBy1 par par', sepBy1P pr pr')

integer' : PP (List Char) Integer
-- would be better to use `some'` here, but it'd require to cast
-- integers into non-empty lists, which is not in the library
integer' = (cast . pack, unpack . cast) <$$> many' (digit, itemP)

spaces' : Stream Char s => PP s ()
spaces' = ignore' (many (oneOf [' ', '\n', '\t', '\r'])) (cons ' ' neutral)
