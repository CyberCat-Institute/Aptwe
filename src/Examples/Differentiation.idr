module Examples.Differentiation

import Data.List.Quantifiers
import IxUtils
import Kernel.Kinds
import Kernel.Types
import Builtins.Types
import Interpreter.Builtins.Types
import Interpreter.Types
import Builtins.Terms
import Kernel.Structure
import Kernel.Terms
import Interpreter.Terms

doubleConst : Double -> Term [] (BaseTy Real)
doubleConst x = BaseTerm $ Builtin $ \[] => (x, \X => [])

times : Term [BaseTy Real, BaseTy Real] (BaseTy Real)
times = BaseTerm $ Builtin $ \[x, y] => (x * y, \X => [X, X])

sin : Term [BaseTy Real] (BaseTy Real)
sin = BaseTerm $ Builtin $ \[x] => (sin x, \X => [X])

cos : Term [BaseTy Real] (BaseTy Real)
cos = BaseTerm $ Builtin $ \[x] => (cos x, \X => [X])

Mono : Ty (True, True) -> Ty (True, True)
Mono a = Tensor a (Not a)

diff : Term [BaseTy Real] (BaseTy Real) -> Term [BaseTy Real] (BaseTy Real)
    -> Term [Mono (BaseTy Real)] (Mono (BaseTy Real))
diff f df = TensorElim Var
          $ Rename (Copy Z $ Insert Id Z $ Insert Id Z $ Empty)
          $ TensorIntro f
          $ NotIntroCov
          $ Rename (Insert Id (S (S Z)) $ Insert Id Z $ Insert Id Z $ Empty)
          $ NotElim Var
          $ Let df
          $ times

dsin : Term [Mono (BaseTy Real)] (Mono (BaseTy Real))
dsin = diff sin cos

dtimes : Term [Mono (BaseTy Real), Mono (BaseTy Real)] (Mono (BaseTy Real))
dtimes = TensorElim Var
       $ Rename (Insert Id (S (S Z)) $ Copy Z $ Insert Id Z $ Insert Id Z $ Empty)
       $ TensorElim Var
       $ Rename (Insert Id (S (S Z)) $ Copy Z $ Insert Id (S (S (S Z))) $ Insert Id Z $ Insert Id Z $ Insert Id Z $ Empty)
       $ TensorIntro times
       $ NotIntroCov
       $ Rename (Insert Id (S Z) $ Insert Id (S (S Z)) $ Copy Z $ Insert Id (S (S Z)) $ Insert Id Z $ Insert Id Z $ Empty)
       $ NotElim Var
       $ UnitElim (NotElim Var $ times)
       $ times

dsquare : Term [Mono (BaseTy Real)] (Mono (BaseTy Real))
dsquare = Rename (Copy Z $ Insert Id Z $ Empty)
         $ dtimes

-- x^2 sin x^2
example : Term [Mono (BaseTy Real)] (Mono (BaseTy Real))
example = Rename (Copy Z $ Insert Id Z $ Empty)
        $ Let (Let dsquare dsin)
        $ dtimes

public export
test : Double -> (Double, Double -> Double)
test x = let ((y, X), k) = eval example [(x, X)]
          in (y, \dy => let [(X, dx)] = k (X, dy) 
                         in dx)
