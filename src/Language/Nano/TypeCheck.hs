{-# LANGUAGE FlexibleInstances, OverloadedStrings, BangPatterns #-}
{-# LANGUAGE InstanceSigs #-}

module Language.Nano.TypeCheck where

import Language.Nano.Types
import Language.Nano.Parser

import qualified Data.List as L
import           Text.Printf (printf)  
import           Control.Exception (throw)

--------------------------------------------------------------------------------
typeOfFile :: FilePath -> IO Type
typeOfFile f = parseFile f >>= typeOfExpr

typeOfString :: String -> IO Type
typeOfString s = typeOfExpr (parseString s)

typeOfExpr :: Expr -> IO Type
typeOfExpr e = do
  let (!st, t) = infer initInferState preludeTypes e
  if (length (stSub st)) < 0 then throw (Error ("count Negative: " ++ show (stCnt st)))
  else return t

--------------------------------------------------------------------------------
-- Problem 1: Warm-up
--------------------------------------------------------------------------------

-- | Things that have free type variables
class HasTVars a where
  freeTVars :: a -> [TId]

-- | Type variables of a type
instance HasTVars Type where
  freeTVars :: Type -> [TId]
  freeTVars TInt = []
  freeTVars TBool = []
  freeTVars (TVar a) = [a]
  freeTVars (TList t) = freeTVars t
  freeTVars (t1 :=> t2) = L.nub (freeTVars t1 ++ freeTVars t2)

-- | Free type variables of a poly-type (remove forall-bound vars)
instance HasTVars Poly where
  freeTVars :: Poly -> [TId]
  freeTVars (Mono t) = freeTVars t
  freeTVars (Forall t p) = L.delete t (freeTVars p)

-- | Free type variables of a type environment
instance HasTVars TypeEnv where
  freeTVars :: TypeEnv -> [TId]
  freeTVars gamma = L.nub (concat [freeTVars s | (x, s) <- gamma])  
  
-- | Look up a variable in a type environment
lookupVarType :: Id -> TypeEnv -> Poly
lookupVarType x ((y, s) : gamma)
  | x == y    = s
  | otherwise = lookupVarType x gamma
lookupVarType x [] = throw (Error ("unbound variable: " ++ x))

-- | Extend a type environment with a new binding
extendTypeEnv :: Id -> Poly -> TypeEnv -> TypeEnv
extendTypeEnv x s gamma = (x,s) : gamma  

-- | Look up a type variable in a substitution;
--   if not present, return the variable unchanged
lookupTVar :: TId -> Subst -> Type
lookupTVar a sub = case lookup a sub of
  Just t  -> t
  Nothing -> TVar a

-- | Remove a type variable from a substitution
removeTVar :: TId -> Subst -> Subst
removeTVar a sub = filter (\(x, _) -> x /= a) sub
     
-- | Things to which type substitutions can be applied
class Substitutable a where
  apply :: Subst -> a -> a
  
-- | Apply substitution to type
instance Substitutable Type where  
  apply :: Subst -> Type -> Type
  apply _   TInt = TInt
  apply _   TBool = TBool
  apply sub (TVar a) = lookupTVar a sub
  apply sub (TList t) = TList (apply sub t)
  apply sub (t1 :=> t2) = apply sub t1 :=> apply sub t2

-- | Apply substitution to poly-type
instance Substitutable Poly where    
  apply :: Subst -> Poly -> Poly
  apply sub (Mono t)     = Mono (apply sub t)
  apply sub (Forall a p) = Forall a (apply (removeTVar a sub) p)

-- | Apply substitution to (all poly-types in) another substitution
instance Substitutable Subst where  
  apply :: Subst -> Subst -> Subst
  apply sub to = zip keys (map (apply sub) vals)
    where
      (keys, vals) = unzip to
      
-- | Apply substitution to a type environment
instance Substitutable TypeEnv where  
  apply :: Subst -> TypeEnv -> TypeEnv
  apply sub gamma = zip keys (map (apply sub) vals)
    where
      (keys, vals) = unzip gamma
      
-- | Extend substitution with a new type assignment
extendSubst :: Subst -> TId -> Type -> Subst
extendSubst sub a t = 
  let t' = apply sub t
  in (a, t') : apply [(a, t')] sub
      
--------------------------------------------------------------------------------
-- Problem 2: Unification
--------------------------------------------------------------------------------
      
-- | State of the type inference algorithm      
data InferState = InferState { 
    stSub :: Subst -- ^ current substitution
  , stCnt :: Int   -- ^ number of fresh type variables generated so far
} deriving (Eq,Show)

-- | Initial state: empty substitution; 0 type variables
initInferState = InferState [] 0

-- | Fresh type variable number n
freshTV n = TVar ("a" ++ show n)
    
-- | Extend the current substitution of a state with a new type assignment   
extendState :: InferState -> TId -> Type -> InferState
extendState (InferState sub n) a t = InferState (extendSubst sub a t) n
        
-- | Unify a type variable with a type; 
--   if successful return an updated state, otherwise throw an error
unifyTVar :: InferState -> TId -> Type -> InferState
unifyTVar st a t 
  | TVar a == t          = st
  | L.elem a (freeTVars t) = throw (Error ("type error: cannot unify " ++ a ++ " and " ++ show t ++ " (occurs check)"))
  | otherwise            = extendState st a t
    
-- | Unify two types;
--   if successful return an updated state, otherwise throw an error
unify :: InferState -> Type -> Type -> InferState
unify st t1 t2 = unify' st (apply (stSub st) t1) (apply (stSub st) t2)
  where
    unify' st TInt TInt = st
    unify' st TBool TBool = st
    unify' st (TVar a) t = unifyTVar st a t
    unify' st t (TVar a) = unifyTVar st a t
    unify' st (TList l) (TList r) = unify st l r
    unify' st (a1 :=> r1) (a2 :=> r2) = 
      let st' = unify st a1 a2
      in unify st' r1 r2
    unify' _ ty1 ty2 = throw (Error ("type error: cannot unify " ++ show ty1 ++ " and " ++ show ty2))

--------------------------------------------------------------------------------
-- Problem 3: Type Inference
--------------------------------------------------------------------------------    
  
infer :: InferState -> TypeEnv -> Expr -> (InferState, Type)
infer st _ (EInt _) = (st, TInt)
infer st _ (EBool _) = (st, TBool)

infer st gamma (EVar x) = 
  let (n', t) = instantiate (stCnt st) (lookupVarType x gamma)
  in (st { stCnt = n' }, t)

infer st gamma (ELam x body) =
  let a = freshTV (stCnt st)
      gamma' = extendTypeEnv x (Mono a) gamma
      (st', tBody) = infer (st { stCnt = stCnt st + 1 }) gamma' body
  in (st', apply (stSub st') (a :=> tBody))

infer st gamma (EApp e1 e2) =
  let (st1, t1) = infer st gamma e1
      (st2, t2) = infer st1 (apply (stSub st1) gamma) e2
      a = freshTV (stCnt st2)
      -- No need to manually apply substitution here anymore!
      st3 = unify (st2 { stCnt = stCnt st2 + 1 }) t1 (t2 :=> a) 
  in (st3, apply (stSub st3) a)

infer st gamma (ELet x e1 e2) =
  let a = freshTV (stCnt st)
      gammaRec = extendTypeEnv x (Mono a) gamma
      (st1, t1) = infer (st { stCnt = stCnt st + 1 }) gammaRec e1
      -- Cleaned up unify call here as well!
      st2 = unify st1 t1 a 
      t1' = apply (stSub st2) t1
      gamma' = apply (stSub st2) gamma
      poly = generalize gamma' t1'
      (st3, t2) = infer st2 (extendTypeEnv x poly gamma') e2
  in (st3, t2)

infer st gamma (EBin op e1 e2) = infer st gamma (EApp (EApp (EVar (opName op)) e1) e2)
  where
    opName Plus  = "+"
    opName Minus = "-"
    opName Mul   = "*"
    opName Eq    = "=="
    opName Ne    = "!="
    opName Lt    = "<"
    opName Le    = "<="
    opName And   = "&&"
    opName Or    = "||"
    opName Cons  = ":"
    opName _     = error "unsupported operator"
    
infer st gamma (EIf cond e1 e2) = infer st gamma (EApp (EApp (EApp (EVar "if") cond) e1) e2)

infer st gamma ENil = infer st gamma (EVar "[]")

-- | Generalize type variables inside a type
generalize :: TypeEnv -> Type -> Poly
generalize gamma t = L.foldr Forall (Mono t) vars
  where
    vars = L.nub (freeTVars t) L.\\ L.nub (freeTVars gamma)
    
-- | Instantiate a polymorphic type into a mono-type with fresh type variables
instantiate :: Int -> Poly -> (Int, Type)
instantiate n s = helper n [] s
  where
    helper :: Int -> Subst -> Poly -> (Int, Type)
    helper n sub (Mono t)     = (n, apply sub t)
    helper n sub (Forall a s) = helper (n + 1) ((a, freshTV n):sub) s
      
-- | Types of built-in operators and functions      
preludeTypes :: TypeEnv
preludeTypes =
  [ ("+",    Mono (TInt :=> TInt :=> TInt))
  , ("-",    Mono (TInt :=> TInt :=> TInt))
  , ("*",    Mono (TInt :=> TInt :=> TInt))
  , ("/",    Mono (TInt :=> TInt :=> TInt))
  , ("==",   Forall "a" (Mono (TVar "a" :=> TVar "a" :=> TBool)))
  , ("!=",   Forall "a" (Mono (TVar "a" :=> TVar "a" :=> TBool)))
  , ("<",    Mono (TInt :=> TInt :=> TBool))
  , ("<=",   Mono (TInt :=> TInt :=> TBool))
  , ("&&",   Mono (TBool :=> TBool :=> TBool))
  , ("||",   Mono (TBool :=> TBool :=> TBool))
  , ("if",   Forall "a" (Mono (TBool :=> TVar "a" :=> TVar "a" :=> TVar "a")))
  , ("[]",   Forall "a" (Mono (TList (TVar "a"))))
  , (":",    Forall "a" (Mono (TVar "a" :=> TList (TVar "a") :=> TList (TVar "a"))))
  , ("head", Forall "a" (Mono (TList (TVar "a") :=> TVar "a")))
  , ("tail", Forall "a" (Mono (TList (TVar "a") :=> TList (TVar "a"))))
  ]
