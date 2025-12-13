{-# LANGUAGE GADTs #-}
{-# LANGUAGE ExistentialQuantification #-}
import Control.Monad (ap, (>=>))
import Debug.Trace (traceShow)

todo :: a
todo = undefined

fatalError :: a
fatalError = error "Fatal error!"

data Val =
    VTt
  | VInt Int
  | VFun (Val -> Term)
  | VKont (Val -> Freer Effect Val)

instance Show Val where
  show (VInt i) = "VInt (" ++ show i ++ ")"
  show (VFun _) = "VFun"
  show (VKont _) = "VKont"

data Term =
    TVal Val
  | TSucc Term
  | TApp Term Term
  | TLet Term (Val -> Term)
  | TPerform String Term
  | THandle Term (Val -> Term) [(String, Val -> Val -> Term)]

ttt :: Term
ttt = TVal VTt

tint :: Int -> Term
tint = TVal . VInt

tfun :: (Val -> Term) -> Term
tfun = TVal . VFun

tseq :: Term -> Term -> Term
tseq t1 t2 = TLet t1 (const t2)

data Freer f a where
  Pure :: a -> Freer f a
  Impure :: f x -> (x -> Freer f a) -> Freer f a

instance Show a => Show (Freer f a) where
  show (Pure x) = "Pure (" ++ show x ++ ")"
  show (Impure _ _) = "Impure"

instance Functor (Freer f) where
  fmap f (Pure x) = Pure (f x)
  fmap f (Impure p k) = Impure p (fmap f . k)

instance Applicative (Freer f) where
  pure = Pure
  (<*>) = ap

instance Monad (Freer f) where
  Pure x >>= f = f x
  Impure p k >>= f = Impure p (k >=> f)

data Effect x where
  Effect :: String -> Val -> Effect Val

handleEffect :: (Val -> Term) -> [(String, Val -> Val -> Term)] -> Freer Effect Val -> Freer Effect Val
handleEffect f _ (Pure x) = interpret (f x)
handleEffect f hs (Impure e@(Effect tag v) k) =
  case lookup tag hs of
    Just h -> interpret (h v (VKont (handleEffect f hs . k)))
    Nothing -> Impure e (handleEffect f hs . k)

interpret :: Term -> Freer Effect Val
interpret (TVal v) = pure v

interpret (TSucc t) = do
  v <- interpret t
  case v of
    VInt i -> Pure (VInt (succ i))
    _ -> fatalError

interpret (TApp t1 t2) = do
  v1 <- interpret t1
  v2 <- interpret t2
  case v1 of
    VFun f -> interpret (f v2)
    VKont f -> f v2
    _ -> fatalError

interpret (TLet t f) = do
  v <- interpret t
  interpret (f v)

interpret (TPerform tag t) = do
  v <- interpret t
  Impure (Effect tag v) Pure

interpret (THandle t1 f hs) = handleEffect f hs (interpret t1)

exampleBody :: Term
exampleBody =
  TPerform "Get" ttt `tseq`
  TPerform "Set" (tint 42) `tseq`
  TPerform "Get" ttt `tseq`
  TPerform "Set" (tint 21) `tseq`
  TPerform "Get" ttt

traceRet x = traceShow ("Ret: " ++ show x)

exampleRet :: Val -> Term
exampleRet x = tfun (\s -> traceRet (x, s) $ TVal x)

traceGet x = traceShow ("Get: " ++ show x)
traceSet x = traceShow ("Set: " ++ show x)

exampleGet :: Val -> Val -> Term
exampleGet _ k = tfun (\x -> traceGet x $ TApp (TApp (TVal k) (TVal x)) (TVal x))

exampleSet :: Val -> Val -> Term
exampleSet x k = tfun (\_ -> traceSet x $ TApp (TApp (TVal k) ttt) (TVal x))

example :: Term
example = TApp (THandle exampleBody exampleRet [("Get", exampleGet), ("Set", exampleSet)]) (tint 0)
