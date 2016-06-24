
module PhysUnit.SIProofs

import PhysUnit.SIUnits


%access public export
%default total


-- Basic postulates about integers
postulate integerAddId : (a : Integer) -> (a + 0) = a
postulate integerMultIf : (a : Integer) -> (a * 1) = a
postulate integerAddInv : (a : Integer) -> (a + negate a) = 0
postulate integerAddComm : (a : Integer) -> (b : Integer) -> (a + b) = (b + a)
postulate integerMultComm : (a : Integer) -> (b : Integer) -> (a * b) = (b * a)
postulate integerAddAssoc : (a : Integer) -> (b : Integer) -> (c : Integer)
                          -> ((a + b) + c) = (a + (b + c))
postulate integerMultAssoc : (a : Integer) -> (b : Integer) -> (c : Integer)
                          -> ((a * b) * c) = (a * (b * c))


vecConsCong2 : {xs : Vect n a} -> {ys : Vect n a} -> x = y -> xs = ys
             -> x :: xs = y :: ys
vecConsCong2 Refl Refl = Refl

vectZipAddComm : (xs : Vect n Integer) -> (ys : Vect n Integer)
               -> zipWith (+) xs ys = zipWith (+) ys xs
vectZipAddComm [] [] = Refl
vectZipAddComm (x::xs) (y::ys) = let r = vectZipAddComm xs ys
                             in
                               vecConsCong2 (integerAddComm x y) r

vectZipAddId : (xs : Vect n Integer) -> zipWith (+) xs (replicate n 0) = xs
vectZipAddId [] = Refl
vectZipAddId (x::xs) = let r = vectZipAddId xs in
                         vecConsCong2 (integerAddId x) r

vectZipAddInv : (xs : Vect n Integer)
  -> zipWith (+) xs (map Interfaces.negate xs) = (replicate n 0)
vectZipAddInv [] = Refl
vectZipAddInv (x::xs) = let r = vectZipAddInv xs in
                          vecConsCong2 (integerAddInv x) r


||| SI unit multiplication is commutative.
siMultComm : (a : SIUnit) -> (b : SIUnit) -> (a *: b) = (b *: a)
siMultComm (MkSIUnit xs) (MkSIUnit ys) = cong (vectZipAddComm xs ys)

||| Multiplying by the zeroUnit gives the original unit.
siMultId : (a : SIUnit) -> (a *: SIUnits.zeroUnit) = a
siMultId (MkSIUnit xs) = cong (vectZipAddId xs)

||| Multiplying a unit by its inverse gives the zero unit.
siInvMult : (a : SIUnit) -> (a *: (invUnit a)) = SIUnits.zeroUnit
siInvMult (MkSIUnit xs) = cong (vectZipAddInv xs)
