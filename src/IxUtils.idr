module IxUtils

import Data.List.Quantifiers

public export
data IxAll : (q : {0 x : a} -> p x -> Type) -> (ys : All p xs) -> Type where
  Nil : {0 q : {x : a} -> p x -> Type} 
     -> IxAll {p} {xs = []} q []
  (::) : {0 q : {x : a} -> p x -> Type}
      -> q y -> IxAll {p} {xs} q ys -> IxAll {p} {xs = x :: xs} q (y :: ys)

namespace IxElem
  public export
  data IxElem : {0 x : a} -> p x -> {0 xs : List a} -> All p xs -> Type where
    Z : IxElem {x = x} a {xs = x :: xs} (a :: as)
    S : IxElem {x} a {xs} bs 
     -> IxElem {x = x} a {xs = x :: xs} (b :: bs)

public export
ixSelect : {0 q : {0 x : a} -> p x -> Type} 
        -> IxElem y ys -> IxAll {p} {xs} q ys -> q y
ixSelect Z (y :: ys) = y
ixSelect (S n) (y :: ys) = ixSelect n ys

namespace IxInsertion
  public export
  data IxInsertion : {0 x : a} -> p x 
                  -> {0 xs : List a} -> All p xs 
                  -> {0 ys : List a} -> All p ys -> Type where
    Z : IxInsertion {x} a {xs} as {ys = x :: xs} (a :: as)
    S : IxInsertion {x} a {xs} as {ys} bs 
     -> IxInsertion {x = x} a {xs = y :: xs} (b :: as) {ys = y :: ys} (b :: bs)

public export
ixInsert : {0 p : a -> Type} -> {0 x : a} -> {0 y : p x}
        -> {0 xs : List a} -> {0 ys : All p xs}
        -> {0 xs' : List a} -> {0 ys' : All p xs'}
        -> {0 q : {0 x : a} -> p x -> Type}
        -> IxInsertion y ys ys' -> q y -> IxAll q ys -> IxAll q ys'
ixInsert Z y ys = y :: ys
ixInsert (S n) y (y' :: ys) = y' :: ixInsert n y ys

public export
ixUnsertL : {0 p : a -> Type} -> {0 x : a} -> {0 y : p x}
         -> {0 xs : List a} -> {0 ys : All p xs}
         -> {0 xs' : List a} -> {0 ys' : All p xs'}
         -> {0 q : {0 x : a} -> p x -> Type}
         -> IxInsertion y ys ys' -> IxAll q ys' -> q y
ixUnsertL Z (y :: ys) = y
ixUnsertL (S n) (y :: ys) = ixUnsertL n ys

public export
ixUnsertR : {0 p : a -> Type} -> {0 x : a} -> {0 y : p x}
         -> {0 xs : List a} -> {0 ys : All p xs}
         -> {0 xs' : List a} -> {0 ys' : All p xs'}
         -> {0 q : {0 x : a} -> p x -> Type}
         -> IxInsertion y ys ys' -> IxAll q ys' -> IxAll q ys
ixUnsertR Z (y :: ys) = ys
ixUnsertR (S n) (y :: ys) = y :: ixUnsertR n ys

namespace IxSimplex
  public export
  data IxSimplex : {0 xs : List a} -> All p xs 
                -> {0 ys : List a} -> All p ys 
                -> {0 zs : List a} -> All p zs -> Type where
    Z : IxSimplex [] bs bs
    S : IxSimplex {xs} as {ys} bs {zs} cs 
     -> IxSimplex {xs = x :: xs} (a :: as) {ys = ys} bs {zs = x :: zs} (a :: cs)

public export
ixSimplex : {xs : List a} -> (as : All p xs)
         -> {ys : List a} -> (bs : All p ys)
         -> (zs : List a ** cs : All p zs ** IxSimplex as bs cs)
ixSimplex {xs = []} [] {ys} bs = (ys ** bs ** Z)
ixSimplex {xs = x :: xs} (a :: as) {ys} bs 
  = let (zs ** cs ** n) = ixSimplex {xs = xs} as {ys = ys} bs 
      in (x :: zs ** a :: cs ** S n)

public export
ixConcat : {0 p : a -> Type} -> {0 as : All p xs} -> {0 bs : All p ys} -> {0 cs : All p zs}
        -> {0 q : {0 x : a} -> p x -> Type}
        -> IxSimplex as bs cs -> IxAll q as -> IxAll q bs -> IxAll q cs
ixConcat Z [] ys = ys
ixConcat (S n) (x :: xs) ys = x :: ixConcat n xs ys

public export
ixUncatL : {0 p : a -> Type} -> {0 as : All p xs} -> {0 bs : All p ys} -> {0 cs : All p zs} 
        -> {0 q : {0 x : a} -> p x -> Type}
        -> IxSimplex as bs cs -> IxAll q cs -> IxAll q as
ixUncatL Z zs = []
ixUncatL (S n) (z :: zs) = z :: (ixUncatL n zs)

public export
ixUncatR : {0 p : a -> Type} -> {0 as : All p xs} -> {0 bs : All p ys} -> {0 cs : All p zs}
        -> {0 q : {0 x : a} -> p x -> Type}
        -> IxSimplex as bs cs -> IxAll q cs -> IxAll q bs
ixUncatR Z zs = zs
ixUncatR (S n) (z :: zs) = ixUncatR n zs
