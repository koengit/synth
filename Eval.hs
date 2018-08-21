module Eval where

import Data.List
import qualified Data.Set as S

--------------------------------------------------------------------------------

data Name
  = If
  | Sel Int
  | Is String
  | Cons String
  | Int Integer
  | Fun String
  | Prim String
  | Var String
  | Crash
 deriving ( Eq, Ord )

instance Show Name where
  show If       = "if"
  show (Sel k)  = "#" ++ show k
  show (Is c)   = "?" ++ c
  show (Cons c) = c
  show (Int n)  = show n
  show (Fun f)  = f
  show (Prim p) = p
  show (Var v)  = v
  show Crash    = "_|_"

--------------------------------------------------------------------------------

data Typ = TApp String [Typ]
 deriving ( Eq, Ord )

instance Show Typ where
  show (TApp t []) = t
  show (TApp t xs) = t ++ "(" ++ intercalate "," (map show xs) ++ ")"

data Symbol =
  Symbol
  { name :: Name
  , args :: [Typ]
  , res  :: Typ
  }
 deriving ( Eq, Ord )

instance Show Symbol where
  show s = show (name s)

arity :: Symbol -> Int
arity f = length (args f)

strarity :: Symbol -> Int
strarity f | name f == If = 1
           | otherwise    = arity f

--------------------------------------------------------------------------------

type Reason r
  = S.Set r

because :: Ord r => r -> Reason r
because r = S.singleton r

data Val r
  = Con (S.Set r) Name [Val r]

true, false, crash :: Ord r => Val r
true  = Con S.empty (Cons "True")  []
false = Con S.empty (Cons "False") []
crash = Con S.empty Crash          []

con :: Val r -> Name
con (Con _ s _) = s

instance Show (Val r) where
  show (Con _ f []) = show f
  show (Con _ f xs) = show f ++ "(" ++ intercalate "," (map show xs) ++ ")"

(<?) :: Ord r => Val r -> Reason r -> Val r
Con r f xs <? r' = Con (r `S.union` r') f xs

why :: Val r -> Reason r
why (Con r _ _) = r

--------------------------------------------------------------------------------

data Expr r
  = App r r Symbol [Expr r]
 deriving ( Eq, Ord )

instance Show (Expr r) where
  show (App _ _ f []) = show f
  show (App _ _ f xs) = show f ++ "(" ++ intercalate "," (map show xs) ++ ")"

eval :: Ord r => Int -> [(String, [String], Expr r)] -> [(String, Val r)] -> Expr r -> (Val r, Int)
eval d _ _ _ | d <= 0 =
  (crash, 0)

eval d prg env (App strf rf f xs) =
  case (name f, xs) of
    (If, [c,x,y]) ->
      case con b of
        Crash        -> (b     <? because strf,        d')
        Cons "True"  -> (vx    <? because rf <? why b, dx)
        Cons "False" -> (vy    <? because rf <? why b, dy)
        _            -> (crash <? because rf <? why b, d')
     where
      (vx,dx) = eval d' prg env x
      (vy,dy) = eval d' prg env y
      (b,d')  = eval d prg env c

    (Var v, []) ->
      (head [ a | (w,a) <- env, w == v ] <? because rf, d)
    
    (f, xs)
      | any ((== Crash) . con) as -> (head [ a | a <- as, con a == Crash ] <? because strf, d')
      | otherwise                 -> (v <? because rf, d2)
     where
      (as,d') = evals d prg env xs
      (v,d2)  = apply d' prg f as
      
      evals d prg env []     = ([],d)
      evals d prg env (x:xs) = (v:vs,d2)
       where
        (v,d')  = eval d prg env x
        (vs,d2) = evals d' prg env xs

apply :: Ord r => Int -> [(String, [String], Expr r)] -> Name -> [Val r] -> (Val r, Int)
apply d prg f as =
  case (f, as) of
    (Sel k, [Con r _ bs])
      | 0 <= k && k < n -> ((bs !! k) <? r, d)
      | otherwise       -> (crash     <? r, d)
     where
      n = length bs
      
    (Is c, [Con r c' _]) ->
      ((if c' == Cons c then true else false) <? r, d)

    (Cons c, as) ->
      (Con S.empty (Cons c) as, d)

    (Int n, []) ->
      (Con S.empty (Int n) [], d)
    
    (Fun f, as) | length as == length xs ->
      eval (d-1) prg (xs `zip` as) rhs
     where
      (xs, rhs):_ = [ (xs,rhs) | (g,xs,rhs) <- prg, g == f ]

    (Prim p, as) ->
      (prim p as, d)

    (Crash, _) ->
      (crash, d)

    _ ->
      error ("apply " ++ show f ++ " of arity " ++ show (length as))

--------------------------------------------------------------------------------

prim :: Ord r => String -> [Val r] -> Val r
prim "term" _ = true

prim "eq" [x,y] = x === y
 where
  Con r1 c1 xs1 === Con r2 c2 xs2
    | c1 == c2 && length xs1 == length xs2 = andl [ x === y | (x,y) <- xs1 `zip` xs2 ] <? r1 <? r2
    | otherwise                            = false <? r1 <? r2

  andl bs
    | any ((== Cons "False") . con) bs = head [ b | b <- bs, con b == Cons "False" ]
    | otherwise                        = true <? S.unions [ r | Con r _ _ <- bs ]

prim "leq" [x,y] = x =<= y
 where
  Con r1 (Int a) [] =<= Con r2 (Int b) []
    | a <= b    = true  <? r1 <? r2
    | otherwise = false <? r1 <? r2

prim "not" [x] = nt x
 where
  nt (Con r (Cons "False") []) = true  <? r
  nt (Con r (Cons "True")  []) = false <? r
  nt x                         = error ("nt " ++ show x)

prim "and" [x,y] = andl [x,y]
 where
  andl bs
    | any ((== Cons "False") . con) bs = head [ b | b <- bs, con b == Cons "False" ]
    | otherwise                        = true <? S.unions [ r | Con r _ _ <- bs ]

prim f xs =
  error ("prim-apply " ++ f ++ " of arity " ++ show (length xs))

--------------------------------------------------------------------------------

enum :: Ord r => Typ -> [Val r]
enum t = concat [ enumSize t n | n <- [0..] ]

enumSize :: Ord r => Typ -> Int -> [Val r]
enumSize (TApp "A" []) n =
  [ Con S.empty (Int (k-1)) []
  | k <- [2^n..2^(n+1)-1]
  ]

enumSize (TApp "Bool" []) n =
  [ x
  | n == 1
  , x <- [ Con S.empty (Cons "False") []
         , Con S.empty (Cons "True") []
         ]
  ]

enumSize t@(TApp "Nat" []) n =
  [ Con S.empty (Cons "Zero") [] | n == 1 ] ++
  [ Con S.empty (Cons "Succ") [u]
  | n > 0
  , u <- enumSize t (n-1)
  ]

enumSize t@(TApp "List" [tx]) n =
  [ Con S.empty (Cons "Nil") [] | n == 1 ] ++
  [ Con S.empty (Cons "Cons") [x,xs]
  | i  <- [0..n-1]
  , x  <- enumSize tx i
  , xs <- enumSize t (n-i-1)
  ]

enumTuple :: Ord r => [Typ] -> [[Val r]]
enumTuple ts = concat [ enumTupleSize ts n | n <- [0..] ]

enumTupleSize :: Ord r => [Typ] -> Int -> [[Val r]]
enumTupleSize []     n = [ [] | n == 0 ]
enumTupleSize (t:ts) n = [ x:xs | i <- [0..n], x <- enumSize t i, xs <- enumTupleSize ts (n-i) ]

--------------------------------------------------------------------------------


