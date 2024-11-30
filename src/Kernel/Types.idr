module Kernel.Types

import Data.List.Quantifiers
import Kernel.Kinds
import Builtins.Types

public export
data Ty : Kind -> Type where
  Unit   : Ty (True, True)
  BaseTy : BaseTy (cov, con) -> Ty (cov, con)
  -- Not x is covariant when x is contravariant
  -- Not x is contravariant when x is covariant
  Not    : Ty (cov, con) -> Ty (con, cov)
  -- Tensor x y is covariant when x is covariant and y is covariant
  -- Tensor x y is contravariant when x is contravariant and y is contravariant
  Tensor : {covx, covy, conx, cony : Bool}
        -> {default (covx && covy) cov : _} -> {default (conx && cony) con : _}
        -> Ty (covx, conx) -> Ty (covy, cony) -> Ty (cov.fst, con.fst)
  -- Hom x y is covariant when x is contravariant and y is covariant
  -- Hom x y is contravariant when x is covariant and y is contravariant
  Hom    : {covx, covy, conx, cony : Bool}
        -> {default (conx && covy) cov : _} -> {default (covx && cony) con : _}
        -> Ty (covx, conx) -> Ty (covy, cony) -> Ty (cov.fst, con.fst)
  -- Par x y is covariant when x is covariant and y is covariant
  -- Par x y is never contravariant
  Par    : {covx, covy, conx, cony : Bool} -> {default (covx && covy) cov : _}
        -> Ty (covx, conx) -> Ty (covy, cony) -> Ty (cov.fst, False)
  Bang   :  Ty (cov, con) -> Ty (cov, con)
