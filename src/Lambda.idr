module Lambda

%access public export

data LambdaTerm' : Type -> Type where 
  Const' : Nat -> LambdaTerm' var
  UF' : String -> LambdaTerm' var
  Var : var -> LambdaTerm' var
  App' : LambdaTerm' var -> LambdaTerm' var -> LambdaTerm' var
  Abs' : (var -> LambdaTerm' var) -> LambdaTerm' var
  
LambdaTerm : Type
LambdaTerm = (var : Type) -> LambdaTerm' var

Eq LambdaTerm where
  x == y = eqLambda' 0 (x Integer) (y Integer)
    where
      eqLambda' : Integer -> LambdaTerm' Integer -> LambdaTerm' Integer -> Bool
      eqLambda' _ (Const' x) (Const' y) = x == y
      eqLambda' _ (UF' x) (UF' y) = x == y
      eqLambda' _ (Var x) (Var y) = x == y
      eqLambda' d (App' f1 x1) (App' f2 x2) = eqLambda' d f1 f2 && eqLambda' d x1 x2
      eqLambda' d (Abs' f) (Abs' g) = eqLambda' (d+1) (f d) (g d)
      eqLambda' _ _ _ = False
      
Ord LambdaTerm where
  compare x y = compareLambda' 0 (x Integer) (y Integer)
    where
      compareLambda' : Integer -> LambdaTerm' Integer -> LambdaTerm' Integer -> Ordering
      compareLambda' _ (Const' x) (Const' y) = compare x y
    
      compareLambda' _ (UF' _) (Const' _) = GT
      compareLambda' _ (UF' x) (UF' y) = compare x y
  
      compareLambda' _ (Var _) (Const' _) = GT
      compareLambda' _ (Var _) (UF' _) = GT
      compareLambda' _ (Var x) (Var y) = compare x y
  
      compareLambda' _ (App' _ _) (Const' _) = GT
      compareLambda' _ (App' _ _) (UF' _) = GT
      compareLambda' _ (App' _ _) (Var _) = GT
      compareLambda' d (App' f1 x1) (App' f2 x2) 
        = compareLambda' d f1 f2 `thenCompare` compareLambda' d x1 x2
  
      compareLambda' _ (Abs' _) (Const' _) = GT
      compareLambda' _ (Abs' _) (UF' _) = GT
      compareLambda' _ (Abs' _) (Var _) = GT
      compareLambda' _ (Abs' _) (App' _ _) = GT
      compareLambda' d (Abs' f) (Abs' g) = compareLambda' (d+1) (f d) (g d)
    
      compareLambda' _ _ _ = LT


LambdaTerm1 : Type
LambdaTerm1 = {var : Type} -> var -> LambdaTerm' var

Const : Nat -> LambdaTerm
Const n = \_ => Const' n

UF : String -> LambdaTerm
UF f = \_ => UF' f

App : LambdaTerm -> LambdaTerm -> LambdaTerm
App f x = \_ => App' (f _) (x _)

Abs : LambdaTerm1 -> LambdaTerm
Abs f = \_ => Abs' f

termToString : LambdaTerm -> String
termToString t = termToString' 0 False (t String)
  where
    needParens : Bool -> String -> String
    needParens True s = "(" ++ s ++ ")"
    needParens _ s = s
    
    termToString' : Nat -> Bool -> LambdaTerm' String -> String
    termToString' _ _ (Const' n) = show n
    termToString' _ _ (UF' s) = s
    termToString' _ _ (Var x) = x
    termToString' ix par (App' (App' f x) y) = needParens par $ 
      let rec = termToString' ix True 
      in unwords [rec f, rec x, rec y]
    termToString' ix par (App' f x) = needParens par $ 
      let rec = termToString' ix True 
      in unwords [rec f, rec x]
    termToString' ix par (Abs' f) = needParens par $ 
      let v = "x" ++ show ix 
      in "\\" ++ v ++ "." ++ termToString' (ix + 1) False (f v)
