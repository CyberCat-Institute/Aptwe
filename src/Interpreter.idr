module Interpreter

import Data.List.Elem
import Data.List.Quantifiers
import IxUtils
import Kernel

-- what standard library is this in?
lookup : Elem x xs -> All p xs -> p x
lookup Here (x :: xs) = x
lookup (There n) (x :: xs) = lookup n xs

public export
data Echo : Type where
  X : Echo

public export
BaseCov : BaseTy con -> Type
BaseCov Nat = Nat
BaseCov Real = Double

mutual
  public export
  Cov : Ty k -> Type
  Cov Unit = Unit
  Cov (Base x) = BaseCov x
  Cov (Not x) = Con x
  Cov (Tensor x y) = (Cov x, Cov y)

  public export
  Con : Ty k -> Type
  Con Unit = Unit
  Con (Base x) = Echo
  Con (Not x) = Cov x
  Con (Tensor x y) = (Con x, Con y)

unit : {x : BaseTy True} -> Cov (Base x)
unit {x = Real} = 0

multiply : {x : BaseTy True} -> Cov (Base x) -> Cov (Base x) -> Cov (Base x)
multiply {x = Real} p q = p + q

mutual
  spawnCov : {x : Ty (cov, True)} -> Cov x
  spawnCov {x = Unit} = ()
  spawnCov {x = Base x} = unit
  spawnCov {x = Not x} = deleteCon
  spawnCov {x = Tensor {con = (True ** and)} x y} with (and)
    spawnCov {x = Tensor {con = (True ** and)} x y} | True 
      = (spawnCov, spawnCov)

  deleteCon : {x : Ty (True, con)} -> Con x
  deleteCon {x = Unit} = ()
  deleteCon {x = Base x} = X
  deleteCon {x = Not x} = spawnCov
  deleteCon {x = Tensor {cov = (True ** and)} x y} with (and)
    deleteCon {x = Tensor {cov = (True ** and)} x y} | True 
      = (deleteCon, deleteCon)

mutual
  mergeCov : {0 cov : Bool} -> {x : Ty (cov, True)} -> Cov x -> Cov x -> Cov x
  mergeCov {x = Unit} () () = ()
  mergeCov {x = Base x} p q = multiply p q
  mergeCov {x = Not x} p q = copyCon p q
  mergeCov {x = Tensor {con = (True ** and)} x y} (p, p') (q, q') with (and)
    mergeCov {x = Tensor {con = (True ** and)} x y} (p, p') (q, q') | True
      = (mergeCov p q, mergeCov p' q')

  copyCon : {0 con : Bool} -> {x : Ty (True, con)} -> Con x -> Con x -> Con x
  copyCon {x = Unit} () () = ()
  copyCon {x = Base x} X X = X
  copyCon {x = Not x} p q = mergeCov p q
  copyCon {x = Tensor {cov = (True ** and)} x y} (p, p') (q, q') with (and)
    copyCon {x = Tensor {cov = (True ** and)} x y} (p, p') (q, q') | True
      = (copyCon p q, copyCon p' q')

parityCov : Parity x y -> Cov x -> Cov y
parityCov Id x = x
parityCov (Raise p) x = parityCov p x
parityCov (Lower p) x = parityCov p x

parityCon : Parity x y -> Con y -> Con x
parityCon Id y = y
parityCon (Raise p) y = parityCon p y
parityCon (Lower p) y = parityCon p y

applyAt : {0 p : a -> Type} -> {y : p x} -> {ys : All p xs}
       -> {0 q : {x : a} -> p x -> Type}
       -> IxElem y ys -> (q y -> q y) -> IxAll q ys -> IxAll q ys
applyAt Z f (x :: xs) = f x :: xs
applyAt (S n) f (x :: xs) = x :: applyAt n f xs

structureCov : Structure xs ys -> IxAll Cov xs -> IxAll Cov ys
structureCov Empty [] = []
structureCov (Insert p i f) xs
  = parityCov p (ixUnsertL i xs) :: structureCov f (ixUnsertR i xs)
structureCov (Delete f) (x :: xs) = structureCov f xs
structureCov (Copy e f) xs = ixSelect e xs :: structureCov f xs
structureCov (Spawn f) xs = spawnCov :: structureCov f xs
structureCov (Merge e f) (x :: xs) = applyAt e (mergeCov x) (structureCov f xs)

structureCon : Structure xs ys -> IxAll Con ys -> IxAll Con xs
structureCon Empty [] = []
structureCon (Insert p i f) (y :: ys)
  = ixInsert i (parityCon p y) (structureCon f ys)
structureCon (Delete f) ys = deleteCon :: structureCon f ys
structureCon (Copy e f) (y :: ys) = applyAt e (copyCon y) (structureCon f ys)
structureCon (Spawn f) (y :: ys) = structureCon f ys
structureCon (Merge e f) ys = ixSelect e ys :: structureCon f ys

public export
eval : Term xs y -> IxAll Cov xs -> (Cov y, Con y -> IxAll Con xs)
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
