module Invincy.Printing
import Data.Vect
import Invincy.Core

%access public export

data Printer : (o, r : Type) -> Type where
  MkPrinter : (r -> o) -> Printer o r

runPrinter : Printer o r -> r -> o
runPrinter (MkPrinter f) = f


infixl 4 >$
interface Contravariant (f: Type -> Type) where
  contramap : (a -> b) -> f b -> f a 
  (>$) : b -> f b -> f a
  (>$) = contramap . const

implementation Contravariant (Printer o) where
  contramap f (MkPrinter p) = MkPrinter $ p . f

interface Contravariant f => Divisible (f: Type -> Type) where
  divide : (a -> (b, c)) -> f b -> f c -> f a
  conquer : f a

implementation Monoid i => Divisible (Printer i) where
  divide p (MkPrinter f) (MkPrinter g) = MkPrinter $ \r => case p r of
    (fi, gi) => f fi <+> g gi
  conquer = MkPrinter $ const neutral

divided : Divisible f => f a -> f b -> f (a, b)
divided = divide id

(*>) : Divisible f => f () -> f a -> f a
(*>) = divide (MkPair ())

(<*) : Divisible f => f a -> f () -> f a
(<*) = divide (flip MkPair ())

interface Divisible f => Decidable (f: Type -> Type) where
  lose : (a -> Void) -> f a
  choose : (a -> Either b c) -> Lazy (f b) -> Lazy (f c) -> f a

implementation Monoid i => Decidable (Printer i) where
  lose _ = conquer
  choose e f g = MkPrinter $ \x => case e x of
    Left fi => runPrinter f fi
    Right gi => runPrinter g gi

chosen : Decidable f => Lazy (f b) -> Lazy (f c) -> f (Either b c)
chosen = choose id


-- could be used for the invertible sat, with no check
itemP : Stream t s => Printer s t
itemP = MkPrinter single

ignoreP : Monoid i => i -> Printer i ()
ignoreP = MkPrinter . const

valP : Stream t s => t -> Printer s ()
valP = ignoreP . single

optionP : Monoid i => a -> Printer i a -> Printer i (Maybe a)
optionP x = contramap (maybe x id)

-- same as manyTill, and perhaps will use for `some`
manyP : Monoid i => Printer i a -> Printer i (List a)
manyP x = MkPrinter $ \l => concatMap (runPrinter x) l

someP : Monoid i => Printer i a -> Printer i (x:List a ** NonEmpty x)
someP = contramap getWitness . manyP

manyTillP : Monoid i => Printer i a -> Printer i () -> Printer i (List a)
manyTillP p t = manyP p <* t

sepBy1P : Monoid i => Printer i a -> Printer i () -> Printer i (x:List a ** NonEmpty x)
sepBy1P p s = MkPrinter $ \(x::xs ** _) => 
  runPrinter p x <+> runPrinter (contramap List.toList (manyP (s *> p))) xs

sepByP : Monoid i => Printer i a -> Printer i () -> Printer i (List a)
sepByP {i} p s = MkPrinter sep
  where
    sep : List a -> i
    sep [] = neutral
    sep (x::xs) = runPrinter (sepBy1P p s) (x::xs ** IsNonEmpty)

integerP : Printer (List Char) Integer
integerP = MkPrinter $ unpack . cast
