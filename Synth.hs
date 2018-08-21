module Main where

import System.IO
import qualified Data.Set as S
import Data.List
import Data.Ord
import SAT hiding ( bool )
import SAT.Val as V
import SAT.Unary as U
import SAT.Bool
import Eval

--------------------------------------------------------------------------------

data Term = Node (V.Val Symbol) [Term]

newTerm :: Solver -> [Symbol] -> Int -> IO Term
newTerm s sig d =
  do sf <- newVal s fs
     ts <- sequence [ newTerm s sig (d-1) | i <- [1..maximum [ arity f | f <- fs ]] ]
     return (Node sf ts)
 where
  fs = [ f | f <- sig, d > 0 || arity f == 0 ]

typeCorrect :: Solver -> Term -> IO ()
typeCorrect s (Node sf xs) =
  do sequence_
       [ addClause s (neg (sf .= f) : [ sx .= x | x <- domain sx, res x == a ])
       | f <- domain sf
       , (a, Node sx _) <- args f `zip` xs
       ]
     sequence_
       [ typeCorrect s x
       | x <- xs
       ]

ifAndCallOnVar :: Solver -> Term -> IO ()
ifAndCallOnVar s x =
  do go SAT.false x
 where
  go v (Node sf xs) =
    do vs <- sequence [ newLit s | x <- xs ]
       sequence_
         [ addClause s [neg (sf .= f), neg v]
         | f <- domain sf
         , (v,i) <- vs `zip` [1..]
         , i > arity f
         ]
       addClause s (neg v : [ sf .= f | f <- domain sf, Var _ <- [name f] ] ++ vs)
       sequence_
         [ addClause s (neg (sf .= f) : ws)
         | f <- domain sf
         , ws <- case name f of
                   If    -> [take 1 vs]
                   Fun _ -> [take (arity f) vs]
                   Sel _ -> [take 1 vs]
                   Is _  -> [take 1 vs]
                   _     -> []
         ]
       sequence_ [ go v x | (v,x) <- vs `zip` xs ]

sane :: Solver -> Term -> IO ()
sane s (Node sf xs) =
  do -- no sel or is on a known constructor
     sequence_
       [ addClause s [neg (sf .= f), neg (sx .= x)]
       | f <- domain sf
       , case name f of
           Sel _ -> True
           Is _  -> True
           _     -> False
       , Node sx _ <- xs
       , x <- domain sx
       , Cons _ <- [name x]
       ]
     sequence_
       [ sane s x
       | x <- xs
       ]

noDoubles :: Solver -> Term -> IO ()
noDoubles s (Node sf xs) =
  do if If `elem` map name (domain sf)
       then do let c:x:y:_ = xs
               c1 <- appears c x
               c2 <- appears c y
               q  <- equal x y
               sequence_
                 [ do addClause s [neg l, neg c1]
                      addClause s [neg l, neg c2]
                      addClause s [neg l, neg q]
                 | f <- domain sf
                 , If <- [name f]
                 , let l = sf .= f
                 ]
               case c of
                 Node sg (y:_) ->
                   do p <- appears y x
                      sequence_
                        [ do addClause s [neg (sf .= f), neg (sg .= g), neg p]
                        | f <- domain sf
                        , If <- [name f]
                        , g <- domain sg
                        , Is _ <- [name g]
                        ]
                 _ -> return ()
       else do return ()
     sequence_
       [ noDoubles s x
       | x <- xs
       ]
 where
  appears c0 x@(Node sf xs) =
    do l <- newLit s
       q <- equal c0 x
       addClause s [neg q, l]
       sequence_
         [ do w <- appears c0 x
              addClause s [neg w, l]
         | x <- xs
         ]
       return l
 
  equal (Node sf xs) (Node sg ys) =
    do qs <- sequence [ equal x y | (x,y) <- xs `zip` ys ]
       q  <- newLit s
       sequence_
         [ addClause s (q : neg (sf .= f) : neg (sg .= f) : map neg (take (arity f) qs))
         | f <- domain sf
         , f `elem` domain sg
         ]
       return q

ifStruct :: Solver -> Term -> IO ()
ifStruct s (Node sf xs) =
  do sequence_
       [ addClause s (neg (sx .= x):[ sf .= f | i > 1, f <- domain sf, If <- [name f]])
       | f <- domain sf
       , (Node sx _,i) <- xs `zip` [1..]
       , x <- domain sx
       , If <- [name x]
       ]
     sequence_
       [ ifStruct s x
       | x <- xs
       ]

isAndSelOnVar :: Solver -> Term -> IO ()
isAndSelOnVar s (Node sf xs) =
  do sequence_
       [ addClause s [neg (sf .= f), neg (sx .= x)]
       | f <- domain sf
       , case name f of
           Is _  -> True
           Sel _ -> True
           _     -> False
       , Node sx _ <- xs
       , x <- domain sx
       , case name x of
           Var _ -> False
           Sel _ -> False
           _     -> True
       ]
     sequence_
       [ isAndSelOnVar s x
       | x <- xs
       ]

onlyRecursion :: Solver -> [(Symbol,[a],Term)] -> IO ()
onlyRecursion s prog =
  do cs <- sequence [ newLit s | _ <- prog ]
     sequence_ [ hasCall c x | (c,(_,_,x)) <- cs `zip` prog ]
     sequence_ [ makesCall (cs `zip` [ f | (f,_,_) <- prog ]) x | (_,_,x) <- prog ]
 where
  hasCall c (Node sf xs) =
    do cs <- sequence [ newLit s | x <- xs ]
       sequence_ [ hasCall c x | (c,x) <- cs `zip` xs ]
       sequence_
         [ addClause s (neg c : [ sf .= f | f <- domain sf, Fun _ <- [name f]]
                             ++ [ neg (sf .= g) ] ++ take (arity g) cs)
         | g <- domain sf
         , case name g of
             Fun _ -> False
             _     -> True
         ]

  makesCall cfs (Node sf xs) =
    do sequence_
         [ addClause s (neg (sf .= f) : [ c | (c,g) <- cfs, g == f ])
         | f <- domain sf
         , Fun _ <- [name f]
         ]
       sequence_ [ makesCall cfs x | x <- xs ]

size :: Solver -> Term -> IO [Lit]
size s (Node sf xs) =
  do xss <- sequence [ size s x | x <- xs ]
     x   <- orl s [ sf .= f | f <- domain sf, hasSize f (name f) ]
     return (x : concat xss)
 where
  hasSize f If       = True
  hasSize f (Fun _)  = True
  --hasSize f (Prim _) = True
  --hasSize f (Cons _) = arity f > 0
  hasSize _ _        = False

--------------------------------------------------------------------------------

type Point = Int

getExpr :: Solver -> Int -> Term -> IO (Expr Point, Int)
getExpr s k (Node sf xs) =
  do f <- V.modelValue s sf
     (es,k') <- getExprs s (k+2) (take (arity f) xs)
     return (App k (k+1) f es,k')
 where
  getExprs s k [] =
    do return ([], k)
  
  getExprs s k (x:xs) =
    do (e, k1) <- getExpr s k x
       (es,k2) <- getExprs s k1 xs
       return (e:es,k2)

data Pat
  = Pat Symbol [Pat]
  | Strict Pat
  | Pat :&: Pat
  | Star
 deriving ( Eq, Ord )

instance Show Pat where
  show (Pat f []) = show f
  show (Pat f xs) = show f ++ "(" ++ intercalate "," (map show xs) ++ ")"
  show (p :&: q)  = show p ++ "&" ++ show q
  show (Strict q) = "!" ++ show q
  show Star       = "*"

pattern :: Solver -> S.Set Int -> Int -> Term -> IO (Pat, Int)
pattern s ps k (Node sf xs) =
  do f <- V.modelValue s sf
     (qs,k') <- patterns s (k+2) (take (arity f) xs)
     return
       ( if (k+1) `S.member` ps
           then Pat f qs
           else if k `S.member` ps
                  then foldr (.&.) Star (map pstrict qs)
                  else Star
       , k'
       )
 where
  patterns s k [] =
    do return ([], k)
  
  patterns s k (x:xs) =
    do (q, k1) <- pattern s ps k x
       (qs,k2) <- patterns s k1 xs
       return (q:qs,k2)

  Star .&. q = q
  q .&. Star = q
  p .&. q    = p :&: q

  pstrict (Strict p) = Strict p
  pstrict Star       = Star
  pstrict (p :&: q)  = pstrict p .&. pstrict q
  pstrict q          = Strict q

match :: Solver -> Pat -> Term -> IO Lit
match s Star _ =
  do return SAT.true

match s (Pat f qs) (Node sf xs) | length qs <= length xs =
  do ls <- sequence [ match s q x | (q,x) <- qs `zip` xs ]
     l  <- newLit s
     addClause s (l : neg (sf .= f) : map neg ls)
     return l

match s (p :&: q) x =
  do l1 <- match s p x
     l2 <- match s q x
     l  <- newLit s
     addClause s [l, neg l1, neg l2]
     return l

match s (Strict q) x@(Node sf xs) =
  do lx <- match s q x
     ls <- sequence [ match s (Strict q) y | y <- xs ]
     l  <- newLit s
     addClause s [l, neg lx]
     sequence_
       [ addClause s [l, neg l', neg (sf .= f)]
       | f  <- domain sf
       , l' <- take (strarity f) ls
       ]
     return l

match s _ _ =
  do return SAT.false

--------------------------------------------------------------------------------

funs :: Expr r -> S.Set Symbol
funs (App _ _ f xs) =
  case name f of
    Fun _ -> S.insert f fs
    _     -> fs
 where
  fs = S.unions (map funs xs)

vars :: Expr r -> S.Set Symbol
vars (App _ _ f xs) =
  case name f of
    Var _ -> S.insert f vs
    _     -> vs
 where
  vs = S.unions (map vars xs)

var :: Typ -> Int -> Symbol
var t i = Symbol (Var (sym t ++ show i)) [] t
 where
  sym (TApp "Bool"  [])  = "q"
  sym (TApp "Bit"   [])  = "b"
  sym (TApp "A"     [])  = "x"
  sym (TApp "Nat"   [])  = "u"
  sym (TApp "List"  [t]) = sym t ++ "s"
  sym (TApp "Maybe" [t]) = "m" ++ sym t

synth :: [Symbol] -> [Expr Point] -> IO ()
synth sig props =
  do putStrLn "-- functions --"
     sequence_ [ putStrLn (show f) | f <- fs ]
     
     s <- newSolver
     prog <- sequence
               [ do rhs@(Node sg _) <- newTerm s sig' depth
                    addClause s [ sg .= g | g <- domain sg, res g == res f ]
                    
                    -- play around with commenting these in/out to restrict the shape of programs
                    typeCorrect s rhs
                    ifAndCallOnVar s rhs
                    sane s rhs
                    noDoubles s rhs
                    ifStruct s rhs
                    --isAndSelOnVar s rhs
                    
                    return (f, vs, rhs)
               | f <- fs
               , let vs   = [ var t i | (t,i) <- args f `zip` [1..] ]
                     sig' = sig ++ fs ++ vs
               ]
     onlyRecursion s prog
     
     ns <- sequence [ do ns <- size s rhs
                         n <- count s ns
                         return n
                    | (_,_,rhs) <- prog
                    ]
     n <- addList s ns
     
     let loop k k' best =
           do b <- sign "SAT" $ solve s (n .<= k : [ n .<= k' | n <- ns ])
              if b then
                do defs <- sequence
                             [ do (e,_) <- getExpr s k rhs
                                  return (show f,map show vs,e)
                             | ((f,vs,rhs),i) <- prog `zip` [1..]
                             , let k = 1000000 * i + 1
                             ]
                   
                   let whys = [ (p,why)
                              | p <- props
                              , Just why <- [test defs p]
                              ]
                   
                       score = length whys
                   
                   sign "TEST" $ seq score $ return ()
                   if score <= best
                     then do putStrLn ("-- program (size=" ++ show k ++", score=" ++ show score ++ ") --")
                             sequence_
                               [ putStrLn ( f ++ "("
                                         ++ intercalate "," vs
                                         ++ ") = "
                                         ++ show e )
                               | (f,vs,e) <- defs
                               ]
                             sequence_
                               [ putStrLn ("FAIL: " ++ show p)
                               | (p,_) <- whys
                               ]
                     else return ()
                   
                   if null whys
                     then do putStrLn "== SOLUTION! =="
                     else do sequence_
                               [ do ps <- sequence
                                            [ do (p,_) <- pattern s why k rhs
                                                 match s p rhs
                                            | ((f,vs,rhs),i) <- prog `zip` [1..]
                                            , let k = 1000000 * i + 1
                                            ]
                                    addClause s (map neg ps)
                               | why <- subsume (map snd whys)
                               ]
                             loop k k' (score `min` best)
               else
                if k >= maxValue n
                  then do putStrLn "== NO SOLUTION =="
                  else do (newk,newk') <-
                            do ls <- conflict s
                               if neg (n .<= k) `elem` ls
                                 then return (k+1,k')
                                 else return (k,k'+1)
                          putStrLn ("== size is now (" ++ show newk ++ "," ++ show newk' ++ ") ==")
                          loop newk newk' best
     
     loop 0 3 (length props + 1)
     deleteSolver s
 where
  fs = S.toList $ S.unions (map funs props)

sign :: String -> IO a -> IO a
sign s h =
  do putStr ("(" ++ s ++ ")")
     hFlush stdout
     x <- h
     putStr (replicate n '\b' ++ replicate n ' ' ++ replicate n '\b')
     hFlush stdout
     return x
 where
  n = length s + 2

subsume :: Ord a => [S.Set a] -> [S.Set a]
subsume ps = go (sortBy (comparing S.size) ps)
 where
  go (p:ps) = p : go (filter (not . (p `S.isSubsetOf`)) ps)
  go []     = []

depth    = 5
maxTests = 300
maxSize  = 10
fuel     = 1000

test :: Ord r => [(String, [String], Expr r)] -> Expr r -> Maybe (S.Set r)
test prog prop =
  case [ why
       | a <- as
       , let (Con why b _, _) = eval fuel prog (map show vs `zip` a) prop
       , b /= name true_
       ] of
    []   -> Nothing
    ps:_ -> Just ps
 where
  vs = S.toList (vars prop)
  as = take maxTests $ concat [ enumTupleSize [ res v | v <- vs ] n | n <- [0..maxSize] ]

propsAppRev =
  [ term (app xs ys)
  , term (rev xs)
  
  , app xs (app ys zs) === app (app xs ys) zs
  , app xs nil === xs
  --, app nil xs === xs
  , app (cons x nil) xs === cons x xs

  --, app (cons x xs) ys === cons x (app xs ys)

  , rev (app xs ys) === app (rev ys) (rev xs)
  , rev nil === nil
  , rev (cons x nil) === cons x nil

  --, rev (cons x xs) === app (rev xs) (cons x nil)
  ]

propsLast =
  [ term (app xs ys)
  , term (last' (cons x xs))
  
  , last' (app xs (cons x nil)) === x
  --, last' (cons x nil) === x
  --, last' (cons x (cons y nil)) === y
  --, last' (cons x (cons y (cons z nil))) === z

  , app xs (app ys zs) === app (app xs ys) zs
  , app xs nil === xs
  -- , app nil xs === xs
  , app (cons x nil) xs === cons x xs
  ]

propsQueue =
  [ term (enq x xs)
  , term (deq xs)
  , term (hd xs)
  , term empty
  
  , hd (enq x empty) === just a x
  , hd (enq x (enq y xs)) === hd (enq y xs)
  , deq (enq x empty) === just (list a) empty
  , deq empty === nothing (list a)
  , unjust (list a) (deq (enq x (enq y xs))) === enq x (unjust (list a) (deq (enq y xs)))
  ]

propsSet =
  [ term (enq x xs)
  , term (member x xs)
  , term empty
  
  --, enq x (enq y xs) === enq y (enq x xs)
  , member z (enq x (enq y xs)) === member z (enq y (enq x xs))
  , member x (enq x xs)
  , nt (member x empty)
  , (member x (enq y xs) === member x xs) ||| (x === y)
  ]

propsPeltier =
  [ term (p u v)
  , term (f u)
  
  , nt (p u u)
  , nt (p u v) ||| nt (p v w) ||| p u w
  , p u (f u)
  --, f u === suc u
  ]

propsGeoff =
  [ term (p u v)
  , term (f u)
  
  , p (f u) u
  , nt (p u v) ||| p (f u) v
  , nt (p u u)
  --, f u === suc u
  ]

propsNonStandard =
  [ term (f u)
  , term (g u)
  , term (h u)
  , term c
  , term d
  
  , nt (c === f u)
  , g (f u) === u
  , (u === c) ||| (u === f (g u))

  , h u === h (f u)
  , nt (h c === h d)
  ]

propsNonStandard2 =
  [ term (f u)
  , term (g u)
  , term (plus u v)
  , term c
  , term d
  --, term e
  
  , nt (c === f u)
  , g (f u) === u
  , (u === c) ||| (u === f (g u))

  , plus c u === u
  , plus (f u) v === f (plus u v)
  --, nt (plus d e === plus e d)
  , nt (plus d c === d)
  ]

propsNonStandardAssoc =
  [ term nil'
  , term (cons' x' xs')
  , term (app' xs' ys')
  , term (hd' xs')
  , term (tl' xs')
  , term as
  , term bs
  , term cs
  
  , nt (nil' === cons' x xs)
  , hd' (cons' x' xs') === x'
  , tl' (cons' x' xs') === xs'
  , (xs' === nil') ||| (xs' === cons' (hd' xs') (tl' xs'))
  
  , app' nil' ys' === ys'
  , app' (cons' x' xs') ys' === cons' x' (app' xs' ys')
  
  , nt (app' as (app' bs cs) === app' (app' as bs) cs)
  ]

--main = synth (boolSig ++ listSig a) propsApp
main = synth (boolSig ++ listSig a ++ [ iff_ a, crash_ a ]) propsLast
--main = synth (boolSig ++ listSig a ++ maybeSig (list a) ++ maybeSig a) propsQueue
--main = synth (boolSig ++ listSig a ++ [ iff_ bool, eq_ a ]) propsSet
--main = synth ([iff_ bool] ++ boolSig ++ natSig) propsPeltier
--main = synth ([iff_ bool] ++ boolSig ++ natSig) propsGeoff
--main = synth (boolSig ++ natSig) propsNonStandard
--main = synth (boolSig ++ natSig) propsNonStandard2

--------------------------------------------------------------------------------

-- types

a       = TApp "A"    []
bit     = TApp "Bit"    []
bool    = TApp "Bool" []
nat     = TApp "Nat" []
list t  = TApp "List" [t]
mayb t  = TApp "Maybe" [t]

list'   = list bool

-- symbols

iff_ t = Symbol If [bool, t, t] t

app_    = Symbol (Fun "app") [list a, list a] (list a)
last_   = Symbol (Fun "last") [list a] a
plus_   = Symbol (Fun "plus") [nat,nat] nat
rev_    = Symbol (Fun "rev") [list a]         (list a)
sort_   = Symbol (Fun "sort") [list a] (list a)
insert_ = Symbol (Fun "insert") [a,list a]         (list a)
enq_   = Symbol (Fun "enq") [a,list a] (list a)
member_ = Symbol (Fun "member") [a,list a] bool
deq_   = Symbol (Fun "deq") [list a]   (mayb (list a))
hd_    = Symbol (Fun "hd") [list a] (mayb a)
empty_ = Symbol (Fun "empty") []         (list a)
eq_ t   = Symbol (Prim "eq") [t, t] bool
leq_ t  = Symbol (Prim "leq") [t, t] bool
term_ t = Symbol (Prim "term") [t] bool
c_      = Symbol (Fun "c") [] nat
f_      = Symbol (Fun "f") [nat] nat
d_      = Symbol (Fun "d") [] nat
e_      = Symbol (Fun "e") [] nat
g_      = Symbol (Fun "g") [nat] nat
h_      = Symbol (Fun "h") [nat] nat
p_      = Symbol (Fun "p") [nat,nat] bool
nt_     = Symbol (Prim "not") [bool] bool
and_    = Symbol (Prim "and") [bool,bool] bool
crash_ t = Symbol Crash [] t

false_ = Symbol (Cons "False") [] bool
true_  = Symbol (Cons "True")  [] bool

b0_ = Symbol (Cons "B0") [] bit
b1_ = Symbol (Cons "B1") [] bit

nil_  t = Symbol (Cons "Nil")  []          (list t)
cons_ t = Symbol (Cons "Cons") [t, list t] (list t)

nil'_  = Symbol (Fun "nil")  []         list'
cons'_ = Symbol (Fun "cons") [bit, list'] list'
hd'_   = Symbol (Fun "hd")   [list'] bit
tl'_   = Symbol (Fun "tl")   [list'] list'
app'_  = Symbol (Fun "app")  [list',list'] list'
as_    = Symbol (Fun "as")   [] list'
bs_    = Symbol (Fun "bs")   [] list'
cs_    = Symbol (Fun "cs")   [] list'

zero_  = Symbol (Cons "Zero") []         nat
suc_  = Symbol (Cons "Succ") [nat] nat

nothing_  t = Symbol (Cons "Nothing")  [] (mayb t)
just_     t = Symbol (Cons "Just") [t] (mayb t)

is_  c   = Symbol (Is (show c)) [res c] bool
sel_ c i = Symbol (Sel i) [res c] (args c !! i)

-- functions

o :: Point
o = 0

app0 a       = App o o a []
app1 f x     = App o o f [x]
app2 f x y   = App o o f [x,y]
app3 f x y z = App o o f [x,y,z]

app     = app2 app_
last'   = app1 last_
rev     = app1 rev_
sort'   = app1 sort_
insert' = app2 insert_

c = app0 c_
f = app1 f_
d = app0 d_
e = app0 e_
g = app1 g_
h = app1 h_
p = app2 p_

plus = app2 plus_

nt    = app1 $ nt_
(&&&) = app2 $ and_
x ||| y = nt (nt x &&& nt y)
(===) = app2 $ eq_ (list a)
(=<=) = app2 $ leq_ a
term  = app1 $ term_ (list a)

nil  = app0 $ nil_ a
cons = app2 $ cons_ a

nil'  = app0 nil'_
cons' = app2 cons'_
hd'   = app1 hd'_
tl'   = app1 tl'_
app'  = app2 app'_
as    = app0 as_
bs    = app0 bs_
cs    = app0 cs_


zero = app0 zero_
suc  = app1 suc_

nothing t = app0 $ nothing_ t
just t    = app1 $ just_ t
unjust t  = app1 $ sel_ (just_ t) 0

enq   = app2 enq_
member = app2 member_
deq   = app1 deq_
hd    = app1 hd_
empty = app0 empty_

-- signatures

boolSig   = [ false_, true_ ] -- , iff_ bool ]
bitSig    = [ b0_, b1_, is_ b0_ ]
natSig    = [ zero_, suc_, is_ zero_, sel_ suc_ 0, iff_ nat ]
leqSig    = [ leq_ a ]
listSig t = [ nil_ t, cons_ t, is_ (nil_ t), sel_ (cons_ t) 0, sel_ (cons_ t) 1, iff_ (list t) ]
maybeSig t = [ nothing_ t, just_ t, is_ (nothing_ t), sel_ (just_ t) 0, iff_ (mayb t) ]

-- variables

x' = app0 $ Symbol (Var "x")  [] bit
x  = app0 $ Symbol (Var "x")  [] a
y  = app0 $ Symbol (Var "y")  [] a
z  = app0 $ Symbol (Var "z")  [] a
u  = app0 $ Symbol (Var "u")  [] nat
v  = app0 $ Symbol (Var "v")  [] nat
w  = app0 $ Symbol (Var "w")  [] nat
xs = app0 $ Symbol (Var "xs") [] (list a)
ys = app0 $ Symbol (Var "ys") [] (list a)
zs = app0 $ Symbol (Var "zs") [] (list a)

xs' = app0 $ Symbol (Var "xs") [] (list bit)
ys' = app0 $ Symbol (Var "ys") [] (list bit)

--------------------------------------------------------------------------------

