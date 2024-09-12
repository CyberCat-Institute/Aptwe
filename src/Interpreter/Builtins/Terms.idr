module Interpreter.Builtins.Terms

import Data.List.Quantifiers
import IxUtils
import Kernel.Kinds
import Kernel.Types
import Builtins.Types
import Builtins.Terms
import Interpreter.Builtins.Types
import Interpreter.Types

public export
evalBaseTerm : BaseTerm xs y -> IxAll Cov xs -> (Cov y, Con y -> IxAll Con xs)
evalBaseTerm BoolAnd [p, q] = (p && q, \X => [X, X])
evalBaseTerm BoolOr [p, q] = (p || q, \X => [X, X])
evalBaseTerm BoolNot [p] = (not p, \X => [X])
evalBaseTerm DoublePlus [p, q] = (p + q, \X => [X, X])
evalBaseTerm DoubleMinus [p, q] = (p - q, \X => [X, X])
evalBaseTerm DoubleTimes [p, q] = (p * q, \X => [X, X])
