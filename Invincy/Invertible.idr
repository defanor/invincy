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
  (a -> Either a a) -> (f a, g a) -> (f a, g a) -> (f a, g a)
choice' e (fa, ga) (fb, gb) = (fa <|> fb, choose e ga gb)


||| Parser and printer
PP : Type -> Type -> Type
PP a b = (Parser a b, Printer a b)

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
ignore' : Monoid i => Parser i a -> i -> PP i ()
ignore' p x = (ignore p, ignoreP x)

||| Parse or print a fixed item
val' : Eq a => a -> PP (List a) ()
val' x = (val x, valP x)

||| Just as val, but for lists
list' : Eq a => List a -> PP (List a) ()
list' l = (list l, ignoreP l)

||| An optional item
||| @a What to print in case if the value is Nothing
option' : Monoid i => a -> PP i a -> PP i (Maybe a)
option' x (par, pr) = (option par, optionP x pr)

many' : Monoid i => PP i a -> PP i (List a)
many' (par, pr) = (many par, manyP pr)

manyTill' : Monoid i => PP i a -> PP i () -> PP i (List a)
manyTill' (par, pr) (par', pr') = (manyTill par par', manyTillP pr pr')

some' : Monoid i => PP i a -> PP i (x:List a ** NonEmpty x)
some' (par, pr) = (some par, someP pr)

sepBy' : Monoid i => PP i a -> PP i () -> PP i (List a)
sepBy' (par, pr) (par', pr') = (sepBy par par', sepByP pr pr')

sepBy1' : Monoid i => PP i a -> PP i () -> PP i (x:List a ** NonEmpty x)
sepBy1' (par, pr) (par', pr') = (sepBy1 par par', sepBy1P pr pr')

integer' : PP (List Char) Integer
-- would be better to use `some'` here, but it'd require to cast
-- integers into non-empty lists, which is not in the library
integer' = (cast . pack, unpack . cast) <$$> many' (digit, itemP)

spaces' : PP (List Char) ()
spaces' = ignore' (many (oneOf [' ', '\n', '\t', '\r'])) [' ']
