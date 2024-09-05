module LawfulLenses

import Data.List.Quantifiers
import IxUtils
import Kernel

public export
prjl : {a, a', b : Ty (True, False)} 
     -> Term [Tensor (Tensor a b) (Not (Tensor a' b))] (Tensor a (Not a'))
prjl = TensorElim Var 
     $ TensorElim Var 
     $ TensorIntro Var 
     $ NotIntro
     $ Rename (Insert Id (S (S Z)) $ Insert Id Z $ Insert Id Z $ Empty)
     $ NotElim Var
     $ TensorIntro Var Var

public export
prjr : {a, b, b' : Ty (True, False)}
    -> Term [Tensor (Tensor a b) (Not (Tensor a b'))] (Tensor b (Not b'))
prjr = TensorElim Var
     $ TensorElim Var
     $ Rename (Insert Id (S Z) $ Insert Id (S Z) $ Insert Id Z $ Empty)
     $ TensorIntro Var
     $ NotIntro
     $ Rename (Insert Id (S Z) $ Insert Id (S Z) $ Insert Id Z $ Empty)
     $ NotElim Var
     $ TensorIntro Var Var
