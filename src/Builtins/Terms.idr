module Builtins.Terms

import Data.List.Quantifiers
import IxUtils
import Kernel.Kinds
import Builtins.Types
import Kernel.Types
import Interpreter.Builtins.Types -- temp
import Interpreter.Types

public export
data BaseTerm : All Ty ks -> Ty k -> Type where
  Builtin : (IxAll Cov xs -> (Cov y, Con y -> IxAll Con xs)) -> BaseTerm xs y
