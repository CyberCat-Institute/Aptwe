module Kernel.Terms

import Data.List.Elem
import Data.List.Quantifiers

import IxUtils
import Kernel.Kinds
import Builtins.Types
import Kernel.Types
import Builtins.Terms
import Kernel.Structure

public export
data Term : All Ty ks -> Ty k -> Type where
  Var : Term [x] x
  BaseTerm : BaseTerm xs y -> Term xs y
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
  HomIntro : Term (x :: xs) y -> Term xs (Hom x y)
  HomElim : {as : All Ty kas} -> {bs : All Ty kbs} -> {default (ixSimplex as bs) cs : _}
         -> Term as (Hom x y) -> Term bs x -> Term (cs.snd.fst) y
  ParIntroL : Term as x -> Term as (Par x y)
  ParIntroR : Term as y -> Term as (Par x y)
  ParElim : {as : All Ty kas} -> {bs : All Ty kbs} -> {default (ixSimplex as bs) cs : _}
         -> Term as (Par x y) -> Term (x :: bs) z -> Term (y :: bs) z -> Term (cs.snd.fst) z
