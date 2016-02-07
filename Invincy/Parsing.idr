module Invincy.Parsing
import Data.Vect

%access public export

mutual
  data Result : (i, r : Type) -> Type where
    Done : Monoid i => i -> r -> Result i r
    Partial : Monoid i => Inf (Parser i r) -> Result i r
    Failure : Monoid i => String -> Result i r

  data Parser : (i, r : Type) -> Type where
    MkParser : ((i -> Result i r)) -> Parser i r

runParser : Parser i r -> ((i -> Result i r))
runParser (MkParser f) = f

implementation Monoid i => Functor (Result i) where
  map f (Done i r) = Done i (f r)
  map f (Partial k) = assert_total (Partial (MkParser $ map f . runParser k))
  map _ f@(Failure s) = f

implementation Monoid i => Functor (Parser i) where
  map f (MkParser k) = MkParser $ (\x => map f $ k x)

implementation Monoid i => Applicative (Parser i) where
  pure x = MkParser (\i => Done i x)
  (MkParser f) <*> g = MkParser $ \i => case f i of
    Done i' f' => case runParser g i' of
      Done i'' r => Done i'' (f' r)
      Partial k => Partial (MkParser $ map f' . runParser k)
      Failure f => Failure f
    Partial k => Partial $ k <*> g
    Failure f => Failure f

infixl 2 <*>|
(<*>|) : Monoid i => Parser i (a -> b) -> Lazy (Parser i a) -> Parser i b
(<*>|) f g = f <*> g

implementation Monoid i => Monad (Parser i) where
  f >>= g = MkParser $ \i => case runParser f i of
    Done i' f' => runParser (g f') i'
    Partial k => Partial $ k >>= g
    f@(Failure s) => f

interface Applicative f => LazyAlternative (f : Type -> Type) where
  empty : f a
  (<|>) : f a -> Lazy (f a) -> f a

implementation Monoid i => LazyAlternative (Parser i) where
  empty = MkParser . const $ Failure "an alternative is empty"
  f <|> g = MkParser $ \i => case (runParser f i) of
    Failure _ => runParser g i
    -- this could probably be improved
    Partial k => Partial $
      let cont = MkParser (\i' => runParser k i');
          next = MkParser (\i' => runParser g (i <+> i'))
      in cont <|> next
    done => done

fail : Monoid i => String -> Parser i r
fail = MkParser . const . Failure

infixl 3 <?>
(<?>) : Monoid i => Parser i a -> String -> Parser i a
(<?>) p s = p <|> fail s

item : Parser (List a) a
item = MkParser $ \i => case i of
  [] => Partial item
  (x::xs) => Done xs x

sat : (a -> Bool) -> Parser (List a) a
sat p = do
  i <- item
  if p i then pure i else fail "sat"

ignore : Monoid i => Parser i a -> Parser i ()
ignore p = p *> pure ()

val : Eq a => a -> Parser (List a) ()
val x = ignore (sat (== x))

list : Eq a => List a -> Parser (List a) ()
list [] = pure ()
list l@(x::xs) = do
  sat (== x)
  list xs
  pure ()

oneOf : Eq a => List a -> Parser (List a) a
oneOf l = sat (flip elem l)

option : Monoid i => Parser i a -> Parser i (Maybe a)
option p = (Just <$> p) <|> (pure Nothing)

manyTill : Monoid i => Parser i a -> Parser i b -> Parser i (List a)
manyTill p t = option t >>= maybe ((<+>) . pure <$> p <*>| manyTill p t) (const $ pure neutral)

many : Monoid i => Parser i a -> Parser i (List a)
many p = option p >>= maybe (pure neutral) (\x => (<+>) . pure <$> pure x <*>| many p)

some : Monoid i => Parser i a -> Parser i (x:List a ** NonEmpty x)
some p = do
  first <- p
  rest <- many p
  pure $ (first :: rest ** IsNonEmpty)
  -- (<+>) . pure <$> p <*> many p

sepBy1 : Monoid i => Parser i a -> Parser i () -> Parser i (x:List a ** NonEmpty x)
sepBy1 x s = do
  first <- x
  rest <- many (s *> x)
  pure $ (first :: rest ** IsNonEmpty)

sepBy : Monoid i => Parser i a -> Parser i () -> Parser i (List a)
sepBy x s = maybe [] getWitness <$> option (sepBy1 x s)

feed : Monoid i => Result i r -> i -> Result i r
feed (Partial k) i = runParser k i
feed (Done i r) i' = Done (i <+> i') r
feed (Failure s) _ = Failure s

digit : Parser (List Char) Char
digit = oneOf ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9']

integer : Parser (List Char) Integer
integer = cast . pack . getWitness <$> some digit


-- feed (feed (runParser ((list ['f', 'o', 'o'] *> pure False) <|> (list ['f', 'o', 'r'] *> pure True)) ['f']) ['o']) ['o']
-- feed (feed (runParser ((list ['f', 'o', 'o'] *> pure False) <|> (list ['f', 'o', 'r'] *> pure True)) ['f']) ['o']) ['r']

parseWith : Monad m => Parser i r -> m i -> m (Result i r)
parseWith p r = do
  v <- r
  case runParser p v of
    Partial k => parseWith k r
    other => pure other
