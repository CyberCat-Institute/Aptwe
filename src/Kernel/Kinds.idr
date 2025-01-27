module Kernel.Kinds

public export
data And : Bool -> Bool -> Bool -> Type where
  True  : And True b b
  False : And False b False

public export total
(&&) : (a, b : Bool) -> (c : Bool ** And a b c)
True  && b = (b ** True)
False && b = (False ** False)

public export total
Kind : Type
Kind = (Bool, Bool)
