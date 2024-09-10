module Kernel

import Data.List.Elem
import Data.List.Quantifiers
import IxUtils

public export
data And : Bool -> Bool -> Bool -> Type where
  True  : And True b b
  False : And False b False

public export
(&&) : (a : Bool) -> (b : Bool) -> (c : Bool ** And a b c)
True  && b = (b ** True)
False && b = (False ** False)

public export
Kind : Type
Kind = (Bool, Bool)

public export
data BaseTy : Bool -> Type where
  Nat : BaseTy False
  Real : BaseTy True

public export
data Ty : Kind -> Type where
  Unit   : Ty (True, True)
  Base   : BaseTy con -> Ty (True, con)
  Not    : Ty (cov, con) -> Ty (con, cov)
  Tensor : {covx, covy, conx, cony : Bool}
        -> {default (covx && covy) cov : _} -> {default (conx && cony) con : _}
        -> Ty (covx, conx) -> Ty (covy, cony) -> Ty (cov.fst, con.fst)

public export
data Parity : Ty (cov, con) -> Ty (cov, con) -> Type where
  Id    : Parity a a
  Raise : Parity a b -> Parity a (Not (Not b))
  Lower : Parity a b -> Parity (Not (Not a)) b

public export
data Structure : All Ty kas -> All Ty kbs -> Type where
  Empty  : Structure [] []
  -- Symmetry is broken here
  Insert : {a, b : Ty (cov, con)} -> {as : All Ty kas} -> {bs : All Ty kbs}
        -> Parity a b -> IxInsertion a as as' -> Structure as bs -> Structure as' (b :: bs)
  Delete : {a : Ty (True, con)} -> Structure as bs -> Structure (a :: as) bs
  Copy   : {a : Ty (True, con)} -> {as : All Ty xs} 
        -> IxElem a as -> Structure as bs -> Structure as (a :: bs)
  Spawn  : {b : Ty (cov, True)} -> Structure as bs -> Structure as (b :: bs)
  Merge  : {b : Ty (cov, True)} -> {bs : All Ty ys} 
        -> IxElem b bs -> Structure as bs -> Structure (b :: as) bs

public export
data Term : All Ty ks -> Ty k -> Type where
  Var : Term [x] x
  Rename : Structure as bs -> Term bs x -> Term as x
  Let : {as : All Ty kas} -> {bs : All Ty kbs} -> {default (ixSimplex as bs) cs : _}
     -> Term as x -> Term (x :: bs) y -> Term cs.snd.fst y
  UnitIntro : Term [] Unit
  UnitElim : {as : All Ty kas} -> {bs : All Ty kbs} -> {default (ixSimplex as bs) cs : _}
          -> Term as Unit -> Term bs x -> Term (cs.snd.fst) x
  NotIntroCov : {a : Ty (True, con)} -> Term (a :: as) Unit -> Term as (Not a)
  NotIntroCon : {a : Ty (cov, True)} -> Term (a :: as) Unit -> Term as (Not a)
  NotElim : {as : All Ty kas} -> {bs : All Ty kbs} -> {default (ixSimplex as bs) cs : _}
         -> Term as (Not x) -> Term bs x -> Term (cs.snd.fst) Unit
  TensorIntro : {as : All Ty kas} -> {bs : All Ty kbs} -> {default (ixSimplex as bs) cs : _}
             -> Term as x -> Term bs y -> Term (cs.snd.fst) (Tensor x y)
  TensorElim : {as : All Ty kas} -> {bs : All Ty kbs} -> {default (ixSimplex as bs) cs : _}
            -> Term as (Tensor x y) -> Term (x :: y :: bs) z -> Term (cs.snd.fst) z
