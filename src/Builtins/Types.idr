module Builtins.Types

import Kernel.Kinds

public export
data BaseTy : Kind -> Type where
  Nat : BaseTy (True, False)
  Bool : BaseTy (True, True)
  Real : BaseTy (True, True)
