module Invincy.Gen
import Language.Reflection.Elab

%access public export

-- todo: multiple and dependent arguments


-- TFoo -> Sigma Type (\x => x -> Foo)

argClause : TTName -> TTName -> (TTName, List CtorArg, Raw) -> 
  (TTName, List CtorArg, Raw) -> FunClause Raw
argClause t' fn (cn, [], _) (en, [], _) =
  MkFunClause (RApp (Var fn) (Var en)) $
    -- `(MkSigma {P=(\x => x -> ~(Var t'))} Unit (\y => ~(Var cn)))
    RApp (RApp `(MkSigma {P=(\x => x -> ~(Var t'))}) (Var "Unit"))
      (RBind "y" (Lam (Var "Unit")) (Var cn))
argClause t' fn (cn, [CtorField ta], _) (en, [], _) = 
  MkFunClause (RApp (Var fn) (Var en)) $
    RApp (RApp `(MkSigma {P=(\x => x -> ~(Var t'))}) (type ta))
      (RBind "y" (Lam (type ta)) (RApp (Var cn) (Var "y")))

cArgs : TTName -> Elab ()
cArgs fn = do
  (_, Ref, sig') <- lookupTyExact fn
  case sig' of
    -- (App _ (Bind _ _ (P _ t' _)))
    (Bind _ (Pi (P _ e' _) _) (App _ (Bind _ (Lam _) (Bind _ (Pi _ _) (P _ t' _))))) => do
      t <- lookupDatatypeExact t'
      e <- lookupDatatypeExact e'
      let clauses = zipWith (argClause t' fn) (constructors t) (constructors e)
      defineFunction $ DefineFun fn clauses
    _ => fail [TextPart "failed", TermPart sig']


-- Foo -> Sigma TFoo (\x => getWitness (args x))

dargClause : Raw -> TTName -> TTName -> (TTName, List CtorArg, Raw) ->
  (TTName, List CtorArg, Raw) -> FunClause Raw
dargClause f t' fn (cn, [], _) (en, [], ent) =
  MkFunClause (RApp (Var fn) (Var cn)) $ 
    RApp (RApp
          `(MkSigma {a=~(ent)} {P=~(f)})
           (Var en))
        `(MkUnit)
dargClause f t' fn (cn, [CtorField x], _) (en, [], ent) =
  MkFunClause (RBind (name x) (PVar (type x)) (RApp (Var fn) (RApp (Var cn) (Var (name x))))) $
    RBind (name x) (PVar (type x)) $
      RApp (RApp `(MkSigma {a=~(ent)} {P=~(f)}) (Var en)) (Var (name x))

dArgs : Raw -> TTName -> Elab ()
dArgs f fn = do
  (_, Ref, sig') <- lookupTyExact fn
  case sig' of
    (Bind _ (Pi (P _ t' _) _) (App (App _ (P _ e' _)) _)) => do
      t <- lookupDatatypeExact t'
      e <- lookupDatatypeExact e'
      let clauses = zipWith (dargClause f t' fn)
                            (constructors t)
                            (constructors e)
      defineFunction $ DefineFun fn clauses
    _ => fail [TextPart "failed", TermPart sig']
