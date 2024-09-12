module Builtins.Terms

import Data.List.Quantifiers
import IxUtils
import Kernel.Kinds
import Builtins.Types
import Kernel.Types

public export
data BaseTerm : All Ty ks -> Ty k -> Type where
  BoolAnd : BaseTerm [BaseTy Bool, BaseTy Bool] (BaseTy Bool)
  BoolOr : BaseTerm [BaseTy Bool, BaseTy Bool] (BaseTy Bool)
  BoolNot : BaseTerm [BaseTy Bool] (BaseTy Bool)
  DoublePlus : BaseTerm [BaseTy Real, BaseTy Real] (BaseTy Real)
  DoubleMinus : BaseTerm [BaseTy Real, BaseTy Real] (BaseTy Real)
  DoubleTimes : BaseTerm [BaseTy Real, BaseTy Real] (BaseTy Real)
