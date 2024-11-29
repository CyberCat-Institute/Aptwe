module Kernel.Types

import Data.List.Quantifiers
import Kernel.Kinds
import Builtins.Types

public export
data Ty : Kind -> Type where
  Unit   : Ty (True, True)
  BaseTy : BaseTy (cov, con) -> Ty (cov, con)
  Not    : Ty (cov, con) -> Ty (con, cov)
  Tensor : {covx, covy, conx, cony : Bool}
        -> {default (covx && covy) cov : _} -> {default (conx && cony) con : _}
        -> Ty (covx, conx) -> Ty (covy, cony) -> Ty (cov.fst, con.fst)
  Hom    : {covx, covy, conx, cony : Bool}
        -> {default (conx && covy) cov : _} -> {default (covx && cony) con : _}
        -> Ty (covx, conx) -> Ty (covy, cony) -> Ty (cov.fst, con.fst)
  Par    : {covx, covy, conx, cony : Bool} -> {default (covx && covy) cov : _}
        -> Ty (covx, conx) -> Ty (covy, cony) -> Ty (cov.fst, False)
