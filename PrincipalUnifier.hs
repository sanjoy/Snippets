{- Toy implementation of a principal (most general) unifier, as in
   TaPL, chapter 22 -}

import Data.List(intercalate)
import Data.Map as M
import Data.Maybe(fromJust)

data Term = NatT | BoolT | VarT String | AbsT String Type Term
          | AppT Term Term deriving(Show, Read)
data Type = NatTy | BoolTy | VarTy String | AbsTy Type Type
          deriving(Read, Eq)

instance Show Type where
  show NatTy       = "Nat"
  show BoolTy      = "Bool"
  show (VarTy s)   = s
  show (AbsTy a b) = "(" ++ (show a) ++ " -> " ++ (show b) ++ ")"

type Context = M.Map String Type
type Constraints = [(Type, Type)]

getConstraints t = let (c, ty, _) = horse eContext fList t in (c, ty)
  where
    fList = Prelude.map (\x->'X':show x) [1..]
    eContext = M.empty
    horse :: Context -> [String] -> Term -> (Constraints, Type, [String])
    horse ctx f NatT  = ([], NatTy, f)
    horse ctx f BoolT = ([], BoolTy, f)
    horse ctx f (VarT s) = ([], fromJust $ M.lookup s ctx, f)
    horse ctx freeList (AbsT s ty term) =
      let newCtx = M.insert s ty ctx
          (constr, newTy, newFList) = horse newCtx freeList term
      in (constr, AbsTy ty newTy, newFList)
    horse ctx (newV:freeList) (AppT t1 t2) =
      let (c1, ty1, f1) = horse ctx freeList t1
          (c2, ty2, f2) = horse ctx f1 t2
      in ((ty1, AbsTy ty2 (VarTy newV)):(c1 ++ c2), VarTy newV, f2)

type Substitutions = [(String, Type)]
unify :: Constraints -> Maybe Substitutions
unify ((s, t):rest) =
  if s == t then unify rest else
    case (s, t) of
      (VarTy x, t) -> combine x t
      (t, VarTy x) -> combine x t
      (AbsTy s1 s2,
       AbsTy t1 t2) -> unify $ (s1, t1):(s2, t2):rest
  where
    replace' x t (a, b) = (replace x t a, replace x t b)
    combine x t = do
      let k = Prelude.map (replace' x t) rest
      r <- unify rest
      if x `isFreeIn` t then Nothing else return $ (x, t):r
    isFreeIn x NatTy = False
    isFreeIn x BoolTy = False
    isFreeIn x (VarTy y) = x == y
    isFreeIn x (AbsTy s t) = x `isFreeIn` s || x `isFreeIn` t
unify [] = Just []

replace x t NatTy  = NatTy
replace x t BoolTy = BoolTy
replace x t (VarTy y) =
  if x == y then t else VarTy y
replace x t (AbsTy a b) = AbsTy (replace x t a) (replace x t b)

getPrincipalType :: Term -> Type
getPrincipalType term =
  let (m, ty) = getConstraints term
      substs  = fromJust $ unify m
  in foldl replace' ty $ reverse substs
  where
    replace' :: Type -> (String, Type) -> Type
    replace' k (a, b) = replace a b k

-- Some example terms.  They taste like lisp. :)
sComb = AbsT "x" (VarTy "X")
        (AbsT "y" (VarTy "Y")
         (AbsT "z" (VarTy "Z")
          (AppT
           (AppT (VarT "x") (VarT "z"))
           (AppT (VarT "y") (VarT "z")))))

m = AbsT "z" (VarTy "ZZ")
    (AbsT "y" (VarTy "YY")
     (AppT (VarT "z")
      (AppT (VarT "y") BoolT)))

-- This should'nt be well-typed under this system.
f = AbsT "f" (VarTy "X") (AppT (o "Y") (o "Z"))
  where
    o k = AbsT "x" (VarTy k) (AppT (VarT "x") (VarT "x"))
