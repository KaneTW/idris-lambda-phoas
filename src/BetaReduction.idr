module BetaReduction

import Lambda
import Debug.Trace

betaReduceLocs : LambdaTerm -> List (List Nat)
betaReduceLocs t = betaReduceLocs' [] (t Integer)
  where
    betaReduceLocs' : List Nat -> LambdaTerm' Integer -> List (List Nat)
    betaReduceLocs' idx (App' (Abs' f) x) = idx :: (betaReduceLocs' (idx ++ [0]) (Abs' f) ++ betaReduceLocs' (idx ++ [1]) x)
    betaReduceLocs' idx (App' f x) = betaReduceLocs' (idx ++ [0]) f ++ betaReduceLocs' (idx ++ [1])  x
    betaReduceLocs' idx (Abs' f) = betaReduceLocs' (idx ++ [2]) (f 0)
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
    betaReduce' (App' (Abs' f) x) [] = f (flattenTerm x)
    betaReduce' (App' f x) (Z :: xs) = App' (betaReduce' f xs) x
    betaReduce' (App' f x) (S Z :: xs) = App' f (betaReduce' x xs)
    betaReduce' (Abs' f) (S (S Z) :: xs) = Abs' $ \x => betaReduce' (f x) xs
    betaReduce' x [] = x
    -- todo: impossibility proof
    betaReduce' x loc = trace ("fail: with loc " ++ show loc) x
 
betaReductionGraph : Nat -> LambdaTerm -> List (LambdaTerm, LambdaTerm)
betaReductionGraph Z _ = []
betaReductionGraph (S d) t with (betaReduceLocs t)
  | [] = []
  | xs = let edg = map (\loc => (t, betaReduce t loc)) (betaReduceLocs t)
         in edg ++ concatMap (betaReductionGraph d . snd) edg



