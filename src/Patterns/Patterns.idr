module Patterns.Patterns

import Data.List.Quantifiers

import Kernel.Kinds
import Kernel.Types

public export
data Pattern : {k : Kind} -> {ks : List Kind} -> Ty k -> All Ty ks -> Type where
  Var : Pattern x [x]
  Unit : Pattern Unit []
  Pair : {covx, conx, covy, cony : Bool}
      -> {x : Ty (covx, conx)} -> {y : Ty (covy, cony)}
      -> Pattern (Tensor x y) [x, y]
  Left : {covx, conx, covy, cony : Bool}
      -> {x : Ty (covx, conx)} -> {y : Ty (covy, cony)}
      -> Pattern (Par x y) [x]
  Right : {covx, conx, covy, cony : Bool}
       -> {x : Ty (covx, conx)} -> {y : Ty (covy, cony)}
       -> Pattern (Par x y) [y]
