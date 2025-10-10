{-# LANGUAGE GADTs #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use newtype instead of data" #-}

import Prelude hiding (reverse)
-- import Debug.Trace (traceShow)

traceShow = const id

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
  | VFun CCF
  | VFix CCF2
  | VPair V V
  | VInl V
  | VInr V

instance Show V where
  show VUnit = "()"
  show (VInt i) = show i
  show (VBool b) = show b
  show (VFun _) = "<fun>"
  show (VFix _) = "<fix>"
  show (VPair v1 v2) = "(" ++ show v1 ++ ", " ++ show v2 ++ ")"
  show (VInl v) = "Inl " ++ show v
  show (VInr v) = "Inr " ++ show v

instance Eq V where
  VUnit == VUnit = True
  VInt i1 == VInt i2 = i1 == i2
  VBool b1 == VBool b2 = b1 == b2
  VPair v11 v12 == VPair v21 v22 = v11 == v21 && v12 == v22
  VInl v1 == VInl v2 = v1 == v2
  VInr v1 == VInr v2 = v1 == v2
  _ == _ = False

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

data CC =
    CCAtom V
  | CCFun CCF
  | CCFix CCF2
  | CCApp V V
  | CCPrim1 Prim1 V
  | CCPrim2 Prim2 V V
  | CCBind CC CCF
  | CCPushPrompt Prompt CC
  | CCTakeSubCont Prompt CCT
  | CCPushSubCont CapturedSubcont V
  | CCPair V V
  | CCSplit V CCF2
  | CCInl V
  | CCInr V
  | CCCase V CCF CCF

data CCF2 = CCF2 (V -> V -> CC)
data CCF = CCF (V -> CC)
data CCT = CCT (CapturedSubcont -> CC)

data Metacont =
    MC0
  | MC1 Prompt Frame Metacont

data CapturedSubcont =
    CSC0 Frame
  | CSC1 Prompt Frame CapturedSubcont

data Frame =
    F0
  | F1 CCF Frame

frameLength :: Frame -> Int
frameLength = go 0
  where
    go acc F0 = acc
    go acc (F1 _ k) = go (succ acc) k

capturedSubcontLength :: CapturedSubcont -> Int
capturedSubcontLength = go 0
  where
    go acc (CSC0 _) = succ acc
    go acc (CSC1 _ _ csk) = go (succ acc) csk

-- THIS IS OUR INTERPRETER
dispatchCC :: CC -> Frame -> Metacont -> V
dispatchCC (CCAtom v) k mk = dispatchFrame k v mk

dispatchCC (CCFun f) k mk = dispatchFrame k (VFun f) mk
dispatchCC (CCFix f) k mk = dispatchFrame k (VFix f) mk
dispatchCC (CCApp v1 v2) k mk = case v1 of
  VFun f -> dispatchCCF f v2 k mk
  VFix f -> dispatchCCF2 f v1 v2 k mk
  _ -> error "Type error"

dispatchCC (CCPrim1 pr v) k mk = dispatchFrame k (prim1 pr v) mk
dispatchCC (CCPrim2 pr v1 v2) k mk = dispatchFrame k (prim2 pr v1 v2) mk
dispatchCC (CCBind m f) k mk = dispatchCC m (F1 f k) mk

dispatchCC (CCPushPrompt p m) k mk = dispatchCC m F0 (MC1 p k mk)
dispatchCC (CCTakeSubCont p body) k mk = takeSubCont p body (CSC0 k) mk
dispatchCC (CCPushSubCont csk v) k mk = pushSubCont csk v k mk

dispatchCC (CCPair v1 v2) k mk = dispatchFrame k (VPair v1 v2) mk
dispatchCC (CCSplit v f) k mk = case v of
  VPair v1 v2 -> dispatchCCF2 f v1 v2 k mk
  _ -> error "Type error"

dispatchCC (CCInl v) k mk = dispatchFrame k (VInl v) mk
dispatchCC (CCInr v) k mk = dispatchFrame k (VInr v) mk
dispatchCC (CCCase v f1 f2) k mk = case v of
  VInl v -> dispatchCCF f1 v k mk
  VInr v -> dispatchCCF f2 v k mk
  _ -> error "Type error"

dispatchCCF2 :: CCF2 -> V -> V -> Frame -> Metacont -> V
dispatchCCF2 (CCF2 f) v1 v2 = dispatchCC (f v1 v2)

dispatchCCF :: CCF -> V -> Frame -> Metacont -> V
dispatchCCF (CCF f) v = dispatchCC (f v)

dispatchCCT :: CCT -> CapturedSubcont -> Frame -> Metacont -> V
dispatchCCT (CCT f) c = dispatchCC (f c)

dispatchFrame :: Frame -> V -> Metacont -> V
dispatchFrame F0 v mk = dispatchMetacont mk v
dispatchFrame (F1 f k) v mk = dispatchCCF f v k mk

dispatchMetacont :: Metacont -> V -> V
dispatchMetacont MC0 v = v
dispatchMetacont (MC1 _ k mk) v = dispatchFrame k v mk

-- split :: Metacont -> Prompt -> (Metacont, Subcont)
-- split MC0 _ = error "Escaping bubble"
-- split (MC1 p sk@(SC k mk)) p' = if p == p' then (MC0, sk) else let (mk', sk') = split mk p' in (MC1 p (SC k mk'), sk')
-- if we do a 'split' operation like this, we need MC0 to "terminate" the sequence
-- how ever, if we do the 'accumulator' style, there is no need for MC0?

takeSubCont :: Prompt -> CCT -> CapturedSubcont -> Metacont -> V
takeSubCont _ _ _ MC0 = error "Escaping bubble"
takeSubCont p body csk (MC1 p' k mk)
  | p == p' = dispatchCCT body csk k mk
  | otherwise = takeSubCont p body (CSC1 p' k csk) mk

-- this is the normal "append"
-- but what if we have a "reverse append"
-- the shape of 'subcont' is now Frame -> Prompt -> Frame ... -> Prompt -> Frame -> MC0
-- the actual shape is Frame -> Prompt -> Frame -> Prompt -> Frame
-- how ever, the only way we can 'execute' captured subcont is with pushSubCont : concatenate the last Frame of captured with the current cont,
-- the push everything into the metacont
appendFrame :: Frame -> Frame -> Frame
appendFrame k1 F0 = k1
appendFrame k1 k2 = appendFrame' k1 k2

appendFrame' :: Frame -> Frame -> Frame
appendFrame' F0 k2 = k2
appendFrame' (F1 f k1') k2 = F1 f (appendFrame' k1' k2)

appendFrameCSK :: Frame -> CapturedSubcont -> CapturedSubcont
appendFrameCSK k (CSC0 k') = CSC0 (appendFrame k' k)
appendFrameCSK k (CSC1 p k' csk) = CSC1 p (appendFrame k' k) csk

pushSubCont :: CapturedSubcont -> V -> Frame -> Metacont -> V
pushSubCont csk v k = pushSubCont' (appendFrameCSK k csk) v

-- this is much more elegant
pushSubCont' :: CapturedSubcont -> V -> Metacont -> V
pushSubCont' (CSC0 k) v mk = dispatchFrame k v mk
pushSubCont' (CSC1 p k csk) v mk = pushSubCont' csk v (MC1 p k mk)

-- -- note that (Frame, Metacont) ~ Subcont
-- -- so, effectively this is "concatenation of two subcont"
-- reverseAppend :: CapturedSubcont -> Frame -> Metacont -> Subcont
-- reverseAppend (CSC0 k)  = append k' mk'

-- append :: Frame -> Metacont -> Frame -> Metacont -> Subcont
-- append k' MC0 k mk = SC (appendFrame k' k) mk
-- append k' (MC1 p sk) k mk = SC k' (MC1 p (append' sk k mk))

-- bind :: CC -> CCF -> Ki -> Kd -> V
-- bind m f ki kd = dispatchCC m (Ki1 f ki kd) (Kd1 kd f)

-- pushPrompt :: Prompt -> CC -> Ki -> Kd -> V
-- pushPrompt p body ki kd = dispatchCC body ki (Kd2 p ki kd)

-- takeSubCont :: Prompt -> CCT -> Ki -> Kd -> V
-- takeSubCont p body _ kd = dispatchKd kd SC0 p body

-- we now want to introduce a better structure for the metacont and the subcont

-- data K =
--     K0
--   | K1 K CCF
--   | K2 Prompt K

-- dispatchKi :: K -> V -> V
-- dispatchKi K0 v = v
-- dispatchKi (K1 k f) v = dispatchCCF f v k
-- dispatchKi (K2 _ k) v = dispatchKi k v

-- dispatchKd :: K -> SubCont -> Prompt -> CCT -> V
-- dispatchKd K0 _ _ _ = error "Escaping bubble"
-- -- "reverse" kd -> subcont
-- dispatchKd (K1 k f) c p body = dispatchKd k (SC1 c f) p body
-- -- either "install" the handler, or "unwind" to find the appropriate handler, while building up the subcont
-- -- we can also "inline" dispatchSubCont here, before "apply" to body
-- -- the goal is to do a single pass over the data, instead of two pass over the data
-- dispatchKd (K2 p' k) c p body
--   | p' == p = dispatchCCT body c k
--   | otherwise = dispatchKd k (SC2 p' c) p body

-- -- a list, where we append continuations to the back and prepend prompt to the front
-- data SubCont =
--     SC0
--   | SC1 SubCont CCF
--   | SC2 Prompt SubCont
-- -- now we note that SubCont is absolutely isomorphic to K

-- -- "rebuild" the structure of the term, from the subcont
-- -- effectively, we are "concatenate" the subcont to the "context"?
-- -- dispatchSubCont :: SubCont -> CC -> CC
-- -- dispatchSubCont SC0 m = m
-- -- dispatchSubCont (SC1 c f) m = CCBind (dispatchSubCont c m) f
-- -- dispatchSubCont (SC2 p c) m = CCPushPrompt p (dispatchSubCont c m)

-- -- dispatchSubCont :: SubCont -> V -> K -> V
-- -- dispatchSubCont SC0 v k = dispatchKi k v
-- -- dispatchSubCont (SC1 c f) v k = dispatchSubCont c v (K1 k f)
-- -- dispatchSubCont (SC2 p c) v k = dispatchSubCont c v (K2 p k)

-- reverseAppend :: SubCont -> K -> K
-- reverseAppend SC0 k = k
-- reverseAppend (SC1 c f) k = reverseAppend c (K1 k f)
-- reverseAppend (SC2 p c) k = reverseAppend c (K2 p k)

-- dispatchSubCont :: SubCont -> V -> K -> V
-- dispatchSubCont c v k = dispatchKi (reverseAppend c k) v

-- and dispatchSubCont becomes "reverse_append"

-- this is because we allow the "argument" of the subcont to be a complex
-- term. If we want to simplify this, the second argument should be an atom only,
-- and then pushSubCont will just call the frames in sequence
-- also, note that this "build" the AST, and then the AST is immediately "consumed"
-- by the interpreter. So this should be promoted into a semantics function, and
-- then we add a syntatic element to represent "the application of a subcont"
-- pushSubCont :: SubCont -> CC -> CC
-- pushSubCont = dispatchSubCont -- decrease 1 index here

runCC :: CC -> V
runCC m = dispatchCC m F0 MC0

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

promptPrompt :: Prompt
promptPrompt = Prompt 2

prompt :: CC -> CC
prompt = CCPushPrompt promptPrompt

control :: ((V -> CC) -> CC) -> CC
control body =
  CCTakeSubCont promptPrompt
    (CCT $ \c -> CCPushPrompt promptPrompt (body $ \v -> CCPushSubCont c v))

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

embed :: [Int] -> V
embed [] = VInl VUnit
embed (x : xs) = VInr (VPair (VInt x) (embed xs))

reverse :: CC
reverse = CCFix
  (CCF2 $ \reverse xs ->
    CCCase xs
      (CCF $ \_ -> CCInl VUnit)
      (CCF $ \xs -> CCSplit xs
        (CCF2 $ \x xs' ->
          CCBind
            (control $ \k ->
              CCBind (k xs')
                (CCF $ \xs' -> CCBind (CCPair x xs')
                  (CCF $ \xs -> CCInr xs)))
            (CCF $ \xs -> CCApp reverse xs))))

reverse1 :: [Int] -> CC
reverse1 xs =
  CCBind reverse
    (CCF $ \reverse -> prompt (CCApp reverse (embed xs)))

copy :: CC
copy = CCFix
  (CCF2 $ \copy xs ->
    CCCase xs
      (CCF $ \_ -> CCInl VUnit)
      (CCF $ \xs -> CCSplit xs
        (CCF2 $ \x xs' ->
          CCBind
            (shift $ \k ->
              CCBind (k xs')
                (CCF $ \xs' -> CCBind (CCPair x xs')
                  (CCF $ \xs -> CCInr xs)))
            (CCF $ \xs -> CCApp copy xs))))

copy1 :: [Int] -> CC
copy1 xs =
  CCBind copy
    (CCF $ \copy -> reset (CCApp copy (embed xs)))

example3 :: CC
example3 = reverse1 (take 10 $ iterate succ 0)

example4 :: CC
example4 = copy1 (take 10 $ iterate succ 0)
