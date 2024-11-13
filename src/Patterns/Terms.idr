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
  Let : {kzs : _} -> {xs : All Ty kxs} -> {ys : All Ty kys} -> {zs : All Ty kzs}
     -> {default (ixSimplex xs zs) xzs : _} -> {default (ixSimplex ys zs) yzs : _}
     -> Term xs a -> Pattern a ys -> Term (yzs.snd.fst) b -> Term (xzs.snd.fst) b
  Unit : Term [] Unit
  Contradiction : {xs : All Ty kxs} -> {ys : All Ty kys}
               -> {default (ixSimplex xs ys) xys : _}
               -> Pattern a xs -> Term (xys.snd.fst) b -> Term ys (Not a) -- todo fix!
  Explosion : {as : All Ty kas} -> {bs : All Ty kbs} -> {default (ixSimplex as bs) cs : _}
           -> Term as (Not x) -> Term bs x -> Term (cs.snd.fst) Unit
  Tensor : {kas, kbs : _} -> {as : All Ty kas} -> {bs : All Ty kbs} -> {default (ixSimplex as bs) cs : _}
        -> Term as x -> Term bs y -> Term (cs.snd.fst) (Tensor x y)
