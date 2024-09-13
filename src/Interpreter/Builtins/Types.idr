module Interpreter.Builtins.Types

import IxUtils
import Kernel.Kinds
import Builtins.Types

public export
EvalBaseTy : BaseTy k -> Type
EvalBaseTy Nat = Nat
EvalBaseTy Bool = Bool
EvalBaseTy Real = Double
