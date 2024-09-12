module Kernel.Structure

import Data.List.Quantifiers
import IxUtils
import Kernel.Kinds
import Kernel.Types

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
