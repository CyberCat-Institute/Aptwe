module Patterns.Terms

import Data.List.Quantifiers

import IxUtils
import Kernel.Kinds
import Kernel.Types
import Builtins.Terms
import Kernel.Structure
import Patterns.Patterns

public export
data Term : All Ty ks -> Ty k -> Type where
  Var : Term [x] x
  BaseTerm : BaseTerm xs y -> Term xs y
  Rename : Structure as bs -> Term bs x -> Term as x
  Let : {kzs : List Kind} -> {xs : All Ty kxs} -> {ys : All Ty kys} -> {zs : All Ty kzs}
     -> {default (ixSimplex xs zs) xzs : _} -> {default (ixSimplex ys zs) yzs : _}
     -> Term xs a -> Pattern a ys -> Term (yzs.snd.fst) b -> Term (xzs.snd.fst) b
  Unit : Term [] Unit
  ContradictionCov : {kxs, kys : List Kind} -> {xs : All Ty kxs} -> {ys : All Ty kys}
                  -> {default (ixSimplex xs ys) xys : _}
                  -> {a : Ty (True, con)}
                  -> Pattern a xs -> Term (xys.snd.fst) Unit -> Term ys (Not a)
  ContradictionCon : {kxs, kys : List Kind} -> {xs : All Ty kxs} -> {ys : All Ty kys}
                  -> {default (ixSimplex xs ys) xys : _}
                  -> {a : Ty (cov, True)}
                  -> Pattern a xs -> Term (xys.snd.fst) Unit -> Term ys (Not a)
  Explosion : {as : All Ty kas} -> {bs : All Ty kbs} -> {default (ixSimplex as bs) cs : _}
           -> Term as (Not x) -> Term bs x -> Term (cs.snd.fst) Unit
  Tensor : {as : All Ty kas} -> {bs : All Ty kbs} -> {default (ixSimplex as bs) cs : _}
        -> Term as x -> Term bs y -> Term (cs.snd.fst) (Tensor x y)
  Lambda : {kas, kbs : List Kind}
        -> {as : All Ty kas} -> {bs : All Ty kbs} -> {default (ixSimplex as bs) cs : _}
        -> Pattern x as -> Term (cs.snd.fst) y -> Term bs (Hom x y)
  App : {as : All Ty kas} -> {bs : All Ty kbs} -> {default (ixSimplex as bs) cs : _}
     -> Term as (Hom x y) -> Term bs x -> Term (cs.snd.fst) y
