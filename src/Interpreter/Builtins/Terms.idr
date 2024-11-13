module Interpreter.Builtins.Terms

import Data.List.Quantifiers
import IxUtils
import Kernel.Kinds
import Kernel.Types
import Builtins.Types
import Builtins.Terms
import Interpreter.Builtins.Types
import Interpreter.Types

public export total
evalBaseTerm : BaseTerm xs y -> IxAll Cov xs -> (Cov y, Con y -> IxAll Con xs)
evalBaseTerm (Builtin f) xs = f xs
