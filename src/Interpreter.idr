module Interpreter

import Data.List.Quantifiers
import IxUtils
import Kernel

public export
data Shadow : Type where
  X : Shadow

mutual
  public export
  Cov : Ty k -> Type
  Cov Unit = Unit
  Cov Ground = Nat
  Cov (Not x) = Con x
  Cov (Tensor x y) = (Cov x, Cov y)

  public export
  Con : Ty k -> Type
  Con Unit = Unit
  Con Ground = Shadow
  Con (Not x) = Cov x
  Con (Tensor x y) = (Con x, Con y)

mutual
  spawnCov : {x : Ty (cov, True)} -> Cov x
  spawnCov {x = Unit} = ()
  spawnCov {x = Not x} = deleteCon
  spawnCov {x = Tensor {con = (True ** and)} x y} with (and)
    spawnCov {x = Tensor {con = (True ** and)} x y} | True = (spawnCov, spawnCov)

  deleteCon : {x : Ty (True, con)} -> Con x
  deleteCon {x = Unit} = ()
  deleteCon {x = Ground} = X
  deleteCon {x = Not x} = spawnCov
  deleteCon {x = Tensor {cov = (True ** and)} x y} with (and)
    deleteCon {x = Tensor {cov = (True ** and)} x y} | True = (deleteCon, deleteCon)

parityCov : Parity x y -> Cov x -> Cov y
parityCov Id x = x
parityCov (Raise p) x = parityCov p x
parityCov (Lower p) x = parityCov p x

parityCon : Parity x y -> Con y -> Con x
parityCon Id y = y
parityCon (Raise p) y = parityCon p y
parityCon (Lower p) y = parityCon p y

structureCov : Structure xs ys -> IxAll Cov xs -> IxAll Cov ys
structureCov Empty [] = []
structureCov (Insert p i f) xs
  = parityCov p (ixUnsertL i xs) :: structureCov f (ixUnsertR i xs)
structureCov (Delete f) (x :: xs) = structureCov f xs
structureCov (Copy e f) xs = ixSelect e xs :: structureCov f xs
structureCov (Spawn f) xs = spawnCov :: structureCov f xs
structureCov (Merge e f) (x :: xs) = structureCov f xs

structureCon : Structure xs ys -> IxAll Con ys -> IxAll Con xs
structureCon Empty [] = []
structureCon (Insert p i f) (y :: ys)
  = ixInsert i (parityCon p y) (structureCon f ys)
structureCon (Delete f) ys = deleteCon :: structureCon f ys
structureCon (Copy e f) (y :: ys) = structureCon f ys
structureCon (Spawn f) (y :: ys) = structureCon f ys
structureCon (Merge e f) ys = ixSelect e ys :: structureCon f ys

public export
eval : Term xs y -> IxAll Cov xs -> (Cov y, Con y -> IxAll Con xs)
eval Var [x] = (x, \y' => [y'])
eval (Rename f t) xs = let (y, k) = eval t (structureCov f xs)
                        in (y, \y' => structureCon f (k y'))
eval UnitIntro [] = ((), \() => [])
eval (NotIntro t) xs 
  = (deleteCon, \x' => let ((), k) = eval t (x' :: xs)
                           y' :: ys = k ()
                        in ys)
eval (UnitElim {cs = (_ ** _ ** s)} t1 t2) xs 
  = let ((), k1) = eval t1 (ixUncatL s xs)
        (y, k2) = eval t2 (ixUncatR s xs)
     in (y, \y' => ixConcat s (k1 ()) (k2 y'))
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
