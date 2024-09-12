module Interpreter.Structure

import Data.List.Quantifiers
import IxUtils
import Kernel.Kinds
import Builtins.Types
import Kernel.Types
import Interpreter.Builtins.Types
import Interpreter.Types
import Kernel.Structure

public export
unit : {x : BaseTy (cov, True)} -> Cov (BaseTy x)
unit {x = Bool} = True
unit {x = Real} = 0

public export
multiply : {x : BaseTy (cov, True)} 
    -> Cov (BaseTy x) -> Cov (BaseTy x) -> Cov (BaseTy x)
multiply {x = Bool} p q = p && q
multiply {x = Real} p q = p + q

mutual
  public export
  spawnCov : {x : Ty (cov, True)} -> Cov x
  spawnCov {x = Unit} = ()
  spawnCov {x = BaseTy x} = unit
  spawnCov {x = Not x} = deleteCon
  spawnCov {x = Tensor {con = (True ** and)} x y} with (and)
    spawnCov {x = Tensor {con = (True ** and)} x y} | True 
      = (spawnCov, spawnCov)

  public export
  deleteCon : {x : Ty (True, con)} -> Con x
  deleteCon {x = Unit} = ()
  deleteCon {x = BaseTy x} = X
  deleteCon {x = Not x} = spawnCov
  deleteCon {x = Tensor {cov = (True ** and)} x y} with (and)
    deleteCon {x = Tensor {cov = (True ** and)} x y} | True 
      = (deleteCon, deleteCon)

mutual
  public export
  mergeCov : {0 cov : Bool} -> {x : Ty (cov, True)} -> Cov x -> Cov x -> Cov x
  mergeCov {x = Unit} () () = ()
  mergeCov {x = BaseTy x} p q = multiply p q
  mergeCov {x = Not x} p q = copyCon p q
  mergeCov {x = Tensor {con = (True ** and)} x y} (p, p') (q, q') with (and)
    mergeCov {x = Tensor {con = (True ** and)} x y} (p, p') (q, q') | True
      = (mergeCov p q, mergeCov p' q')

  public export
  copyCon : {0 con : Bool} -> {x : Ty (True, con)} -> Con x -> Con x -> Con x
  copyCon {x = Unit} () () = ()
  copyCon {x = BaseTy x} X X = X
  copyCon {x = Not x} p q = mergeCov p q
  copyCon {x = Tensor {cov = (True ** and)} x y} (p, p') (q, q') with (and)
    copyCon {x = Tensor {cov = (True ** and)} x y} (p, p') (q, q') | True
      = (copyCon p q, copyCon p' q')

public export
parityCov : Parity x y -> Cov x -> Cov y
parityCov Id x = x
parityCov (Raise p) x = parityCov p x
parityCov (Lower p) x = parityCov p x

public export
parityCon : Parity x y -> Con y -> Con x
parityCon Id y = y
parityCon (Raise p) y = parityCon p y
parityCon (Lower p) y = parityCon p y

public export
applyAt : {0 p : a -> Type} -> {y : p x} -> {ys : All p xs}
       -> {0 q : {x : a} -> p x -> Type}
       -> IxElem y ys -> (q y -> q y) -> IxAll q ys -> IxAll q ys
applyAt Z f (x :: xs) = f x :: xs
applyAt (S n) f (x :: xs) = x :: applyAt n f xs

public export
structureCov : Structure xs ys -> IxAll Cov xs -> IxAll Cov ys
structureCov Empty [] = []
structureCov (Insert p i f) xs
  = parityCov p (ixUnsertL i xs) :: structureCov f (ixUnsertR i xs)
structureCov (Delete f) (x :: xs) = structureCov f xs
structureCov (Copy e f) xs = ixSelect e xs :: structureCov f xs
structureCov (Spawn f) xs = spawnCov :: structureCov f xs
structureCov (Merge e f) (x :: xs) = applyAt e (mergeCov x) (structureCov f xs)

public export
structureCon : Structure xs ys -> IxAll Con ys -> IxAll Con xs
structureCon Empty [] = []
structureCon (Insert p i f) (y :: ys)
  = ixInsert i (parityCon p y) (structureCon f ys)
structureCon (Delete f) ys = deleteCon :: structureCon f ys
structureCon (Copy e f) (y :: ys) = applyAt e (copyCon y) (structureCon f ys)
structureCon (Spawn f) (y :: ys) = structureCon f ys
structureCon (Merge e f) ys = ixSelect e ys :: structureCon f ys
