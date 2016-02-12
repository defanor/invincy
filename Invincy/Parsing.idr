module Invincy.Parsing
import Data.Vect
import Invincy.Core

%access public export


mutual
  data Result : (i, r : Type) -> Type where
    Done : Stream t s => s -> r -> Result s r
    Partial : Stream t s => Inf (Parser s r) -> Result s r
    Failure : Stream t s => String -> Result s r

  data Parser : (i, r : Type) -> Type  where
    MkParser : Stream t s => ((s -> Result s r)) -> Parser s r


runParser : Parser s r -> ((s -> Result s r))
runParser (MkParser f) = f

implementation Stream t s => Functor (Result s) where
  map f (Done i r) = Done i (f r)
  map f (Partial k) = assert_total (Partial (MkParser $ map f . runParser k))
  map _ f@(Failure s) = f

implementation Functor (Parser s) where
  map f (MkParser k) = MkParser $ (\x => map f $ k x)

implementation Stream t s => Applicative (Parser s) where
  pure x = MkParser (\i => Done i x)
  (MkParser f) <*> g = MkParser $ \i => case f i of
    Done i' f' => case runParser g i' of
      Done i'' r => Done i'' (f' r)
      Partial k => Partial (MkParser $ map f' . runParser k)
      Failure f => Failure f
    Partial k => Partial $ k <*> g
    Failure f => Failure f

infixl 2 <*>|
(<*>|) : Stream t s => Parser s (a -> b) -> Lazy (Parser s a) -> Parser s b
(<*>|) f g = f <*> g

implementation Stream t s => Monad (Parser s) where
  f >>= g = MkParser $ \i => case runParser f i of
    Done i' f' => runParser (g f') i'
    Partial k => Partial $ k >>= g
    f@(Failure s) => f

interface Applicative f => LazyAlternative (f : Type -> Type) where
  empty : f a
  (<|>) : f a -> Lazy (f a) -> f a

implementation Stream t s => LazyAlternative (Parser s) where
  empty = MkParser . const $ Failure "an alternative is empty"
  f <|> g = MkParser $ \i => case (runParser f i) of
    Failure _ => runParser g i
    -- this could probably be improved
    Partial k => Partial $
      let cont = MkParser (\i' => runParser k i');
          next = MkParser (\i' => runParser g (i <+> i'))
      in cont <|> next
    done => done

fail : Stream t s => String -> Parser s r
fail = MkParser . const . Failure

infixl 3 <?>
(<?>) : Stream t s => Parser s a -> String -> Parser s a
(<?>) p s = p <|> fail s

item : Stream t s => Parser s t
item = MkParser $ \i => case uncons i of
  Nothing => Partial item
  Just (x, xs) => Done xs x

sat : Stream t s => (t -> Bool) -> Parser s t
sat p = do
  i <- item
  if p i then pure i else fail "sat"

ignore : Stream t s => Parser s a -> Parser s ()
ignore p = p *> pure ()

val : (Eq t, Stream t s) => t -> Parser s ()
val x = ignore (sat (== x))

raw : (Eq t, Stream t s) => s -> Parser s ()
raw l = case uncons l of
  Nothing => pure ()
  Just (x, xs) => do
    sat (== x)
    raw xs
    pure ()

oneOf : (Eq t, Stream t s) => List t -> Parser s t
oneOf l = sat (flip elem l)

option : Stream t s => Parser s a -> Parser s (Maybe a)
option p = (Just <$> p) <|> (pure Nothing)

manyTill : Stream t s => Parser s a -> Parser s b -> Parser s (List a)
manyTill p t = option t >>= maybe ((<+>) . pure <$> p <*>| manyTill p t) (const $ pure neutral)

many : Stream t s => Parser s a -> Parser s (List a)
many p = option p >>= maybe (pure neutral) (\x => (<+>) . pure <$> pure x <*>| many p)

some : Stream t s => Parser s a -> Parser s (x:List a ** NonEmpty x)
some p = do
  first <- p
  rest <- many p
  pure $ (first :: rest ** IsNonEmpty)

sepBy1 : Stream t s => Parser s a -> Parser s () -> Parser s (x:List a ** NonEmpty x)
sepBy1 x s = do
  first <- x
  rest <- many (s *> x)
  pure $ (first :: rest ** IsNonEmpty)

sepBy : Stream t s => Parser s a -> Parser s () -> Parser s (List a)
sepBy x s = maybe [] getWitness <$> option (sepBy1 x s)

feed : Stream t s => Result s r -> s -> Result s r
feed (Partial k) i = runParser k i
feed (Done i r) i' = Done (i <+> i') r
feed (Failure s) _ = Failure s

digit : Stream Char s => Parser s Char
digit = oneOf ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9']

integer : Stream Char s => Parser s Integer
integer = cast . pack . getWitness <$> some digit


-- feed (feed (runParser ((list ['f', 'o', 'o'] *> pure False) <|> (list ['f', 'o', 'r'] *> pure True)) ['f']) ['o']) ['o']
-- feed (feed (runParser ((list ['f', 'o', 'o'] *> pure False) <|> (list ['f', 'o', 'r'] *> pure True)) ['f']) ['o']) ['r']

parseWith : Monad m => Parser s r -> m s -> m (Result s r)
parseWith p r = do
  v <- r
  case runParser p v of
    Partial k => parseWith k r
    other => pure other
