module Patterns.Elaborator

import Data.List.Quantifiers

import IxUtils
import Kernel.Kinds
import Kernel.Types
import Patterns.Patterns
import Patterns.Terms
import Kernel.Terms

total
act : {kys : List Kind} -> {xs : All Ty kxs} -> {ys : All Ty kys} -> IxSimplex xs ys xys
   -> Pattern a xs -> Kernel.Terms.Term xys b -> Kernel.Terms.Term (a :: ys) b
act (S Z) Var t = t
act Z Unit t = UnitElim Var t 
act (S (S Z)) Pair t = TensorElim Var t 

elaborator : Patterns.Terms.Term xs a -> Kernel.Terms.Term xs a
elaborator Var = Var
elaborator (BaseTerm x) = BaseTerm x
elaborator (Rename s t) = Rename s (elaborator t)
elaborator (Let {xzs, yzs} t1 p t2) = Let {cs = xzs} (elaborator t1) (act (yzs.snd.snd) p (elaborator t2))
elaborator Unit = UnitIntro
elaborator (Contradiction x y) = ?fixme
elaborator (Explosion {cs} t1 t2) = NotElim {cs} (elaborator t1) (elaborator t2)
elaborator (Tensor {cs} t1 t2) = TensorIntro {cs} (elaborator t1) (elaborator t2)
