module Data.Permutation.Permutation

import Data.So
import Data.List
import Control.Order
import Data.List.Elem
import Data.List.Quantifiers
import Data.Nat
import Data.Nat.Order
import Data.Nat.Views
import Data.Vect

public export
data Permutation : (xs : List a) -> (xs': List a) -> Type where 
    PermNil : Permutation [] []  
    PermCons : Permutation xs xs' -> Permutation (x :: xs) (x :: xs')
    PermSwap : Permutation (x :: y :: xs) (y :: x :: xs)
    PermTrans : {ys : List a} -> Permutation xs ys -> Permutation ys zs -> Permutation xs zs  

public export
permRefl : {xs : List a} -> Permutation xs xs
permRefl {xs = []} = PermNil 
permRefl {xs = (_ :: xs)} = PermCons permRefl {xs = xs}

public export
permSym : Permutation xs ys -> Permutation ys xs
permSym PermNil = PermNil 
permSym (PermCons xs) = PermCons (permSym xs) 
permSym PermSwap = PermSwap 
permSym (PermTrans x y) = PermTrans (permSym y) (permSym x)

public export
data Partition : (x: Nat) -> (xs: List Nat) -> Type where
    MkPartition : {ys, zs: List Nat}
      -> All (\x => LTE x p) ys -- p is bigger than all elements in ys
      -> All (\x => LTE p x) zs -- p is smaller than all elements in zs
      -> Permutation xs (ys ++ zs) -- if xs is a permutation of ys ++ zs, then
      -> Partition p xs -- p is the pivot, xs is the original list

-- if xs is a permutation of xs', then we can concatenate zs to both
public export
permConcat : {xs, xs', zs: List a}
  -> Permutation xs xs' -> Permutation (xs ++ zs) (xs' ++ zs)
permConcat PermNil = permRefl 
permConcat (PermCons xs) = PermCons (permConcat xs) 
permConcat PermSwap = PermSwap 
permConcat (PermTrans p1 p2) = PermTrans (permConcat p1) (permConcat p2)


-- from two lists, we can concatenate them in two ways. They're permutations of each other
public export
permCommutative : (xs, ys: List a)
  -> Permutation (xs ++ ys) (ys ++ xs)
permCommutative {xs = xs} {ys = []}
  = rewrite appendNilRightNeutral xs in permRefl 
permCommutative {xs = []} {ys = (y :: ys)} = rewrite appendNilRightNeutral ys
                                             in permRefl 
permCommutative {xs = (x :: xs)} {ys = (y :: ys)} = PermTrans p1 p2 where
    ih1 = permCommutative xs ys
    ih2 = permCommutative (x::xs) ys
    ih3 = permCommutative xs (y::ys)
    p1 = PermCons $ PermTrans ih3 (PermCons (permSym ih1))
    p2 = PermTrans PermSwap (PermCons ih2)

public export
permConcatReverse : {xs, xs', zs: List a} -> Permutation xs xs' -> Permutation (zs ++ xs) (zs ++ xs')
permConcatReverse px = 
    let p1 = permConcat px {zs=zs}
        p2 = permCommutative {xs=xs} {ys=zs}
        p3 = PermTrans (permSym p1) p2
    in PermTrans (permSym p3) (permCommutative {xs=xs'} {ys=zs})

public export
permConcatTrans : {xs, xs', ys, ys' : List a}
    -> Permutation xs xs'
    -> Permutation ys ys'
    -> Permutation (xs ++ ys) (xs' ++ ys')
permConcatTrans PermNil py = py 
permConcatTrans (PermCons px) py
  = PermCons (permConcatTrans px py) 
permConcatTrans PermSwap py
  = PermTrans PermSwap (PermCons (PermCons (permConcatReverse py)))
permConcatTrans (PermTrans x y) py = PermTrans (PermTrans ih1 p1) ih2 where
        ih1 = permConcatTrans x py
        ih2 = permConcatTrans y py
        p1 = permSym (permConcatReverse py)
       

public export
permLemma : {x: a} -> {xs, ys, zs: List a}
  -> Permutation xs (ys ++ zs)
  -> Permutation (x :: xs) (ys ++ (x :: zs))
permLemma perm = PermTrans (PermCons {x=x} $ PermTrans perm (permCommutative {xs=ys} {ys=zs})) (permCommutative {xs=(x::zs)} {ys=ys})

public export
partition : (p: Nat) -> (xs: List Nat) -> Partition p xs 
partition p [] = MkPartition [] [] PermNil   
partition p (x :: xs) = case lte x p of
    Yes lte => let (MkPartition allLte allGte perm) = partition p xs
               in MkPartition (lte::allLte) allGte (PermCons perm)
    No pf => let (MkPartition allLte allGte perm) = partition p xs
                 gte = lteSuccLeft $ notLTEImpliesGT pf
             in MkPartition allLte (gte::allGte) (permLemma perm) 

public export
permAll : All p xs -> Permutation xs ws -> All p ws 
permAll (x :: y :: xs) PermSwap = y :: x :: xs  
permAll all PermNil = [] 
permAll (x :: xs) (PermCons c) = x :: permAll xs c
permAll all (PermTrans a b) = permAll (permAll all a) b


-- If all elements in a list satisfy a property, then the last element also satisfies it
public export
lastAll : {p : a -> Type} -> {xs: List a} -> {auto pf: NonEmpty xs}
  -> All p xs -> p (last xs)
lastAll [] impossible
lastAll [pTerm] = pTerm
lastAll (pTerm :: pTerms) = case pTerms of
    [] => pTerm
    (q :: qs) => lastAll (q :: qs)

public export
lteIfExists : (xs : List Nat) -> (n : Nat) -> Type
lteIfExists [] n = ()
lteIfExists (x :: xs) n = LTE (last (x :: xs)) n
