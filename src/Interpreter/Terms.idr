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

public export total
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
eval (HomIntro t) xs = (\x => let (y, k) = eval t (x :: xs)
                               in (y, \y' => let x' :: _ = k y'
                                              in x'),
                        \(x, y') => let (y, k) = eval t (x :: xs)
                                        _ :: xs' = k y'
                                     in xs')
eval (HomElim {cs = (_ ** _ ** s)} t1 t2) xs 
  = let (f, k1) = eval t1 (ixUncatL s xs)
        (x, k2) = eval t2 (ixUncatR s xs)
        (y, k3) = f x
     in (y, \y' => ixConcat s (k1 (x, y')) (k2 (k3 y')))
eval (ParIntroL t) xs
  = let (y, k) = eval t xs
     in (Left y, \(f, _) => k (f y))
eval (ParIntroR t) xs
  = let (y, k) = eval t xs
     in (Right y, \(_, f) => k (f y))
eval (ParElim {cs = (_ ** _ ** s)} t1 t2 t3) xs
  = case eval t1 (ixUncatL s xs) of
      (Left x, k1) => let (z, k2) = eval t2 (x :: ixUncatR s xs)
                       in (z, \z' => let x' :: xs' = k2 z'
                                         f = \y => let (_, k3) = eval t3 (y :: ixUncatR s xs)
                                                    in k3 z'
                                      in ixConcat s (k1 (const x', f)) xs')
      (Right y, k1) => let (z, k2) = eval t3 (y :: ixUncatR s xs)
                        in (z, \z' => let y' :: xs' = k2 z'
                                          f = \x => let (_, k3) = eval t2 (x :: ixUncatR s xs)
                                                     in k3 z'
                                       in ixConcat s (k1 (f, const y')) xs')
