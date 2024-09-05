module Kernel

import Data.List.Quantifiers
import IxUtils

data And : Bool -> Bool -> Bool -> Type where
  True  : And True b b
  False : And False b False

(&&) : (a : Bool) -> (b : Bool) -> (c : Bool ** And a b c)
True  && b = (b ** True)
False && b = (False ** False)

Kind : Type
Kind = (Bool, Bool)

data Ty : Kind -> Type where
  Unit   : Ty (True, True)
  Ground : Ty (True, False)
  Not    : Ty (cov, con) -> Ty (con, cov)
  Tensor : {covx, covy, conx, cony : Bool}
        -> {default (covx && covy) cov : _} -> {default (conx && cony) con : _}
        -> Ty (covx, conx) -> Ty (covy, cony) -> Ty (cov.fst, con.fst)

data Parity : Ty (cov, con) -> Ty (cov, con) -> Type where
  Id    : Parity a a
  Raise : Parity a b -> Parity a (Not (Not b))
  Lower : Parity a b -> Parity (Not (Not a)) b

data Structure : All Ty kas -> All Ty kbs -> Type where
  Empty  : Structure [] []
  -- Symmetry is broken here
  Insert : {a, b : Ty (cov, con)} -> {as : All Ty kas} -> {bs : All Ty kbs}
        -> Parity a b -> IxInsertion b bs cs -> Structure as bs -> Structure (a :: as) cs
  Delete : {a : Ty (True, con)} -> Structure as bs -> Structure (a :: as) bs
  Copy   : {a : Ty (True, con)} -> {as : All Ty xs} 
        -> IxElem {xs = xs} a as -> Structure as bs -> Structure as (a :: bs)
  Spawn  : {b : Ty (cov, True)} -> Structure as bs -> Structure as (b :: bs)
  Merge  : {b : Ty (cov, True)} -> {bs : All Ty ys} 
        -> IxElem {xs = ys} b bs -> Structure as bs -> Structure (b :: as) bs

data Term : All Ty ks -> Ty k -> Type where
  Var : Term [x] x
  Rename : Structure as bs -> Term bs x -> Term as x
  UnitIntro : Term [] Unit
  UnitElim : {as : All Ty kas} -> {bs : All Ty kbs} -> {default (ixSimplex as bs) cs : _}
          -> Term as Unit -> Term bs x -> Term (cs.snd.fst) x
  NotElim : {as : All Ty kas} -> {bs : All Ty kbs} -> {default (ixSimplex as bs) cs : _}
         -> Term as (Not x) -> Term bs x -> Term (cs.snd.fst) Unit
  TensorIntro : {as : All Ty kas} -> {bs : All Ty kbs} -> {default (ixSimplex as bs) cs : _}
             -> Term as x -> Term bs y -> Term (cs.snd.fst) (Tensor x y)
  TensorElim : {as : All Ty kas} -> {bs : All Ty kbs} -> {default (ixSimplex as bs) cs : _}
            -> Term as (Tensor x y) -> Term (x :: y :: bs) z -> Term (cs.snd.fst) z
