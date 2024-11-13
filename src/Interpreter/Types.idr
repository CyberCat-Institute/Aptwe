module Interpreter.Types

import Kernel.Kinds
import Builtins.Types
import Kernel.Types
import Interpreter.Builtins.Types

public export
data Echo : Type where
  X : Echo

mutual
  public export total
  Cov : Ty k -> Type
  Cov Unit = Unit
  Cov (BaseTy x) = EvalBaseTy x
  Cov (Not x) = Con x
  Cov (Tensor x y) = (Cov x, Cov y)

  public export total
  Con : Ty k -> Type
  Con Unit = Unit
  Con (BaseTy x) = Echo
  Con (Not x) = Cov x
  Con (Tensor x y) = (Con x, Con y)
