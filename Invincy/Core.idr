module Invincy.Core

%access public export


interface Monoid s => Stream t s | s where
  single : t -> s
  uncons : s -> Maybe (t, s)
  cons : t -> s -> s
  cons x s = single x <+> s
  

implementation Stream t (List t) where
  single = pure
  uncons (x::xs) = Just (x, xs)
  uncons [] = Nothing
  cons = (::)

implementation Stream Char String where
  single = singleton
  uncons s = case strM s of
    StrNil => Nothing
    StrCons x xs => Just (x, xs)
  cons = strCons


fromString : Stream Char s => String -> s
fromString = concatMap single . unpack
