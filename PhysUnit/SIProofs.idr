
module PhysUnit.SIProofs

import PhysUnit.SIUnits


%access private
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
postulate integerDblEven : (a : Integer) -> Even (a + a)


vecConsCong2 : {xs : Vect n a} -> {ys : Vect n a} -> x = y -> xs = ys
  -> x :: xs = y :: ys
vecConsCong2 Refl Refl = Refl

vectZipAddComm : (xs : Vect n Integer) -> (ys : Vect n Integer)
  -> zipWith (+) xs ys = zipWith (+) ys xs
vectZipAddComm [] [] = Refl
vectZipAddComm (x::xs) (y::ys) = let r = vectZipAddComm xs ys
                                 in vecConsCong2 (integerAddComm x y) r

vectZipAddAssoc : (xs : Vect n Integer) -> (ys : Vect n Integer)
  -> (zs : Vect n Integer)
  -> zipWith (+) (zipWith (+) xs ys) zs = zipWith (+) xs (zipWith (+) ys zs)
vectZipAddAssoc [] [] [] = Refl
vectZipAddAssoc (x::xs) (y::ys) (z::zs)
  = let r = vectZipAddAssoc xs ys zs
    in vecConsCong2 (integerAddAssoc x y z) r

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
export
siMultComm : (a : SIUnit) -> (b : SIUnit) -> (a *: b) = (b *: a)
siMultComm (MkSIUnit xs) (MkSIUnit ys) = cong (vectZipAddComm xs ys)

||| SI unit multiplication is associative.
export
siMultAssoc : (a : SIUnit) -> (b : SIUnit) -> (c : SIUnit)
  -> (a *: b) *: c = a *: (b *: c)
siMultAssoc (MkSIUnit xs) (MkSIUnit ys) (MkSIUnit zs)
  = cong (vectZipAddAssoc xs ys zs)

||| Multiplying by the zeroUnit gives the original unit.
export
siMultId : (a : SIUnit) -> (a *: SIUnits.zeroUnit) = a
siMultId (MkSIUnit xs) = cong (vectZipAddId xs)

||| Multiplying a unit by its inverse gives the zero unit.
export
siInvMult : (a : SIUnit) -> (a *: (invUnit a)) = SIUnits.zeroUnit
siInvMult (MkSIUnit xs) = cong (vectZipAddInv xs)

||| Any unit raised to the zeroth power is equal to the zero unit.
export
siPowZero : (a : SIUnit) -> (a ^: 0) = SIUnits.zeroUnit
siPowZero _ = Refl

||| Any unit raised to the first power is equal to that unit.
export
siPowOne : (a : SIUnit) -> (a ^: 1) = a
siPowOne u = siMultId u

||| The square of unit equals that unit times itself.
export
siSqrEqMult : (a : SIUnit) -> (a ^: 2) = (a *: a)
siSqrEqMult u = let lem1 = sym (siMultAssoc u u zeroUnit)
                    lem2 = siMultId (u *: u)
                in trans lem1 lem2

||| The square of a unit is even.
export
siSqrEven : (a : SIUnit) -> SIEven (a ^: 2)
siSqrEven u@(MkSIUnit [m, kg, s, a, k, cd, mol])
  = let mprf = integerDblEven m
        kgprf = integerDblEven kg
        sprf = integerDblEven s
        aprf = integerDblEven a
        kprf = integerDblEven k
        cdprf = integerDblEven cd
        molprf = integerDblEven mol
        prf = MkSIEven mprf kgprf sprf aprf kprf cdprf molprf
    in replace (sym $ siSqrEqMult u) prf

--siSqrtInv : (a : SIUnit) -> sqrtUnit {ev = siSqrEven a} (a ^: 2) = a
--siSqrtInv u = ?ssiprf
