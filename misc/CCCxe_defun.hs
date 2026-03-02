{-# LANGUAGE GADTs #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use newtype instead of data" #-}

todo :: a
todo = undefined

newtype Prompt = Prompt Int deriving (Show, Eq)

data Prim1 =
    P1Not
  | P1Neg

data Prim2 =
    P2Add
  | P2Mul
  | P2And
  | P2Or
  | P2Eq

data V =
    VUnit
  | VInt Int
  | VBool Bool
  deriving (Show, Eq)

data CC =
    CCAtom V
  | CCPrim1 Prim1 V
  | CCPrim2 Prim2 V V
  | CCBind CC CCF
  | CCPushPrompt Prompt CC
  | CCTakeSubCont Prompt CCT
  | CCPushSubCont SubCont V

prim1 :: Prim1 -> V -> V
prim1 P1Neg (VInt i) = VInt (negate i)
prim1 P1Not (VBool b) = VBool (not b)
prim1 _ _ = error "Type error"

prim2 :: Prim2 -> V -> V -> V
prim2 P2Add (VInt i1) (VInt i2) = VInt (i1 + i2)
prim2 P2Mul (VInt i1) (VInt i2) = VInt (i1 * i2)
prim2 P2And (VBool b1) (VBool b2) = VBool (b1 && b2)
prim2 P2Or (VBool b1) (VBool b2) = VBool (b1 || b2)
prim2 P2Eq v1 v2 = VBool (v1 == v2)
prim2 _ _ _ = error "Type error"

-- THIS IS OUR INTERPRETER
dispatchCC :: CC -> Ki -> Kd -> V
dispatchCC (CCAtom v) ki kd = dispatchKi ki v
dispatchCC (CCPrim1 pr v) ki kd = dispatchKi ki (prim1 pr v)
dispatchCC (CCPrim2 pr v1 v2) ki kd = dispatchKi ki (prim2 pr v1 v2)
dispatchCC (CCBind m f) ki kd = dispatchCC m (Ki1 f ki kd) (Kd1 kd f)
-- this is already structurally recursive, because
-- we "recurse" on m, which is a subterm of (CCPushPrompt p m)
dispatchCC (CCPushPrompt p m) ki kd = dispatchCC m ki (Kd2 p ki kd)
-- can inline takeSubCont here, and then inline dispatchKd here
-- then it would be "structurally recursive" over the call graph
-- (Bove-Capretta method)
-- however, takeSubCont "introduce" a new variable (subcont - SC0)
-- so the current signature of dispatchCC is not compatible
dispatchCC (CCTakeSubCont p body) _ kd = dispatchKd kd SC0 p body
dispatchCC (CCPushSubCont c v) ki kd = dispatchSubCont c v ki kd

-- bind :: CC -> CCF -> Ki -> Kd -> V
-- bind m f ki kd = dispatchCC m (Ki1 f ki kd) (Kd1 kd f)

-- pushPrompt :: Prompt -> CC -> Ki -> Kd -> V
-- pushPrompt p body ki kd = dispatchCC body ki (Kd2 p ki kd)

-- takeSubCont :: Prompt -> CCT -> Ki -> Kd -> V
-- takeSubCont p body _ kd = dispatchKd kd SC0 p body

dispatchKi :: Ki -> V -> V
dispatchKi Ki0 a = a
dispatchKi (Ki1 f ki kd) a = dispatchCCF f a ki kd

dispatchKd :: Kd -> SubCont -> Prompt -> CCT -> V
dispatchKd Kd0 _ _ _ = error "Escaping bubble"
-- "reverse" kd -> subcont
dispatchKd (Kd1 kd f) c p body = dispatchKd kd (SC1 c f) p body
-- either "install" the handler, or "unwind" to find the appropriate handler, while building up the subcont
-- we can also "inline" dispatchSubCont here, before "apply" to body
-- the goal is to do a single pass over the data, instead of two pass over the data
dispatchKd (Kd2 p' ki kd) c p body
  | p' == p = dispatchCCT body c ki kd
  | otherwise = dispatchKd kd (SC2 p' c) p body

data CCF = CCF (V -> CC)
data CCT = CCT (SubCont -> CC)

dispatchCCF :: CCF -> V -> Ki -> Kd -> V
dispatchCCF (CCF f) v = dispatchCC (f v)

dispatchCCT :: CCT -> SubCont -> Ki -> Kd -> V
dispatchCCT (CCT f) c = dispatchCC (f c)

-- a list, where we append continuations to the back and prepend prompt to the front
data SubCont =
    SC0
  | SC1 SubCont CCF
  | SC2 Prompt SubCont

-- "rebuild" the structure of the term, from the subcont
-- effectively, we are "concatenate" the subcont to the "context"?
-- dispatchSubCont :: SubCont -> CC -> CC
-- dispatchSubCont SC0 m = m
-- dispatchSubCont (SC1 c f) m = CCBind (dispatchSubCont c m) f
-- dispatchSubCont (SC2 p c) m = CCPushPrompt p (dispatchSubCont c m)

dispatchSubCont :: SubCont -> V -> Ki -> Kd -> V
dispatchSubCont SC0 v ki kd = dispatchKi ki v
dispatchSubCont (SC1 c f) v ki kd = dispatchSubCont c v (Ki1 f ki kd) (Kd1 kd f)
dispatchSubCont (SC2 p c) v ki kd = dispatchSubCont c v ki (Kd2 p ki kd)

data Ki =
    Ki0
  | Ki1 CCF Ki Kd

data Kd =
    Kd0 -- error "Escaping bubble"
  | Kd1 Kd CCF -- (\c -> kd ((>>= f) . c))
  | Kd2 Prompt Ki Kd -- \c body -> case proj p body of ...

-- this is because we allow the "argument" of the subcont to be a complex
-- term. If we want to simplify this, the second argument should be an atom only,
-- and then pushSubCont will just call the frames in sequence
-- also, note that this "build" the AST, and then the AST is immediately "consumed"
-- by the interpreter. So this should be promoted into a semantics function, and
-- then we add a syntatic element to represent "the application of a subcont"
-- pushSubCont :: SubCont -> CC -> CC
-- pushSubCont = dispatchSubCont -- decrease 1 index here

runCC :: CC -> V
runCC m = dispatchCC m Ki0 Kd0

resetPrompt :: Prompt
resetPrompt = Prompt 0

reset :: CC -> CC
reset = CCPushPrompt resetPrompt

shift :: ((V -> CC) -> CC) -> CC
shift body =
  CCTakeSubCont resetPrompt
    (CCT $ \c -> CCPushPrompt resetPrompt
      (body $ \v -> CCPushPrompt resetPrompt (CCPushSubCont c v)))

reset0Prompt :: Prompt
reset0Prompt = Prompt 1

reset0 :: CC -> CC
reset0 = CCPushPrompt reset0Prompt

shift0 :: ((V -> CC) -> CC) -> CC
shift0 body =
  CCTakeSubCont reset0Prompt
    (CCT $ \c -> body $ \v -> CCPushPrompt resetPrompt (CCPushSubCont c v))

example :: CC
example = CCBind
  (reset $
    CCBind
    (shift $ \k ->
      CCBind
        (k $ VInt 6)
        (CCF $ \x ->
          CCBind
            (k $ VInt 9)
            (CCF $ \y -> CCPrim2 P2Add x y)))
    (CCF $ \v -> CCPrim2 P2Add (VInt 10) v)) (CCF $ \z ->
  CCPrim2 P2Mul (VInt 5) z)

example2 :: CC
example2 = CCBind
  (CCBind
    (shift $ \k ->
      CCBind
        (k $ VInt 6)
        (CCF $ \x ->
          CCBind
            (k $ VInt 9)
            (CCF $ \y -> CCPrim2 P2Add x y)))
    (CCF $ \v -> CCPrim2 P2Add (VInt 10) v))
  (CCF $ \z -> CCPrim2 P2Mul (VInt 5) z)
