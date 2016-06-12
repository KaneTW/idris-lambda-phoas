module BetaReduction

import Lambda

betaReduceLocs : LambdaTerm -> List (List Nat)
betaReduceLocs t = betaReduceLocs' 0 (t Integer)
  where
    betaReduceLocs' : Nat -> LambdaTerm' Integer -> List (List Nat)
    betaReduceLocs' idx (App' (Abs' f) x) = [[idx]] ++ map (idx ::) (betaReduceLocs' 0 (f 0) ++ betaReduceLocs' 1 x)
    betaReduceLocs' idx (App' f x) = map (idx ::) (betaReduceLocs' 0 f ++ betaReduceLocs' 1 x)
    betaReduceLocs' idx (Abs' f) = map (idx ::) (betaReduceLocs' 0 (f 0))
    betaReduceLocs' _ _ = []

flattenTerm : LambdaTerm' (LambdaTerm' var) -> LambdaTerm' var
flattenTerm (Const' n) = Const' n
flattenTerm (UF' x) = UF' x
flattenTerm (Var x) = x
flattenTerm (App' f x) = App' (flattenTerm f) (flattenTerm x)
flattenTerm (Abs' f) = Abs' $ \x => flattenTerm (f (Var x))

substituteVar : LambdaTerm1 -> LambdaTerm -> LambdaTerm
substituteVar f x = \_ => flattenTerm (f (x _))


betaReduce : LambdaTerm -> List Nat -> LambdaTerm
betaReduce t loc = \_ => flattenTerm (betaReduce' (t (LambdaTerm' _)) loc)
  where 
    betaReduce' : LambdaTerm' (LambdaTerm' var) -> List Nat -> LambdaTerm' (LambdaTerm' var)
    betaReduce' (App' (Abs' f) x) [_] = f (flattenTerm x)
    betaReduce' (App' f x) (O :: xs) = App' (betaReduce' f xs) x
    betaReduce' (App' f x) (S O :: xs) = App' f (betaReduce' x xs)
    betaReduce' (Abs' f) (_ :: xs) = Abs' $ \x => betaReduce' (f x) xs
    betaReduce' x _ = x
 

