
module PhysUnit.Quantity

import PhysUnit.SIUnits


%access export
%default total


||| A quantity is the combination of magnitude and a unit.
data Quantity : Type -> SIUnit -> Type where
  MkQuant : {u : SIUnit} -> a -> Quantity a u

public export
DQuantity : SIUnit -> Type
DQuantity = Quantity Double

infixr 5 =|
||| Constructs a quantity.
(=|) : a -> (u : SIUnit) -> Quantity a u
(=|) x _ = MkQuant x

(Show a) => Show (Quantity a u) where
    show (MkQuant x) = (show x) ++ " " ++ (show u)


infixr 6 :+
(:+) : (Num a) => Quantity a u -> Quantity a u -> Quantity a u
(:+) (MkQuant x) (MkQuant y) = MkQuant (x + y)

infixr 6 :-
(:-) : (Neg a) => Quantity a u -> Quantity a u -> Quantity a u
(:-) (MkQuant x) (MkQuant y) = MkQuant (x - y)

infixr 7 :*
(:*) : (Num a) => Quantity a u1 -> Quantity a u2 -> Quantity a (u1 *: u2)
(:*) (MkQuant x) (MkQuant y) = MkQuant (x * y)

infixr 7 :/
(:/) : (Fractional a) => Quantity a u1 -> Quantity a u2 -> Quantity a (u1 /: u2)
(:/) (MkQuant x) (MkQuant y) = MkQuant (x / y)

-- TODO: Make total
infixr 8 :^
partial
(:^) : (Fractional a, Num a) => Quantity a u -> (n : Integer)
  -> Quantity a (u ^: n)
(:^) (MkQuant x) n = MkQuant (pow' x n)
  where
    pow' x n = if n < 0 then pow' (recip x) (-n)
               else if n == 0 then 1
               else x * (pow' x (n - 1))

||| Takes the square root of a quantity.
||| Requires evidence that the unit is composed of base units raised to even
||| powers.
sqrtQ : Quantity Double u -> {auto ev : SIEven u}
      -> Quantity Double (sqrtUnit {ev = ev} u)
sqrtQ (MkQuant x) = MkQuant (sqrt x)
