module Interpreter.Terms

import Data.List.Elem
import Data.List.Quantifiers
import IxUtils
import Kernel.Kinds
import Builtins.Types
import Kernel.Types
import Builtins.Terms
import Kernel.Terms
import Interpreter.Builtins.Types
import Interpreter.Types
import Interpreter.Builtins.Terms
import Interpreter.Structure

public export
eval : Term xs y -> IxAll Cov xs -> (Cov y, Con y -> IxAll Con xs)
eval (BaseTerm t) xs = evalBaseTerm t xs
eval Var [x] = (x, \y' => [y'])
eval (Rename f t) xs = let (y, k) = eval t (structureCov f xs)
                        in (y, \y' => structureCon f (k y'))
eval (Let {cs = (_ ** _ ** s)} t1 t2) xs
  = let (y, k1) = eval t1 (ixUncatL s xs)
        (z, k2) = eval t2 (y :: ixUncatR s xs)
     in (z, \z' => let y' :: ys' = k2 z'
                    in ixConcat s (k1 y') ys')
eval UnitIntro [] = ((), \() => [])
eval (UnitElim {cs = (_ ** _ ** s)} t1 t2) xs 
  = let ((), k1) = eval t1 (ixUncatL s xs)
        (y, k2) = eval t2 (ixUncatR s xs)
     in (y, \y' => ixConcat s (k1 ()) (k2 y'))
eval (NotIntroCov t) xs 
  = (deleteCon, \x' => let ((), k) = eval t (x' :: xs)
                           y' :: ys = k ()
                        in ys)
eval (NotIntroCon t) xs 
  = let ((), k) = eval t (spawnCov :: xs) 
        y :: ys = k ()
     in (y, \y' => ys)
eval (NotElim {cs = (_ ** _ ** s)} t1 t2) xs 
  = let (y1, k1) = eval t1 (ixUncatL s xs)
        (y2, k2) = eval t2 (ixUncatR s xs)
     in ((), \() => ixConcat s (k1 y2) (k2 y1))
eval (TensorIntro {cs = (_ ** _ ** s)} t1 t2) xs 
  = let (y1, k1) = eval t1 (ixUncatL s xs)
        (y2, k2) = eval t2 (ixUncatR s xs)
     in ((y1, y2), \(y1', y2') => ixConcat s (k1 y1') (k2 y2'))
eval (TensorElim {cs = (_ ** _ ** s)} t1 t2) xs 
  = let ((y1, y2), k1) = eval t1 (ixUncatL s xs)
        (y2, k2) = eval t2 (y1 :: y2 :: (ixUncatR s xs))
     in (y2, \y' => let x1' :: x2' :: xs' = k2 y'
                     in ixConcat s (k1 (x1', x2')) xs')
