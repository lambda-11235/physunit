
module PhysUnit.SIUnits

import PhysUnit.Even

import Data.Vect


%access public export
%default total


||| SI unit represented with seven integers, each representing the powers of the
||| base units. The order is meter, kilogram, second, ampere, kelvin, candela,
||| and lastly mole.
data SIUnit : Type where
  MkSIUnit : Vect 7 Integer -> SIUnit

data SIEven : SIUnit -> Type where
  MkSIEven : Even m -> Even kg -> Even s -> Even a -> Even k -> Even cd
           -> Even mol -> SIEven (MkSIUnit [m, kg, s, a, k, cd, mol])

zeroUnit : SIUnit
zeroUnit = MkSIUnit [0, 0, 0, 0, 0, 0, 0]

invUnit : SIUnit -> SIUnit
invUnit (MkSIUnit xs) = MkSIUnit $ map negate xs

sqrtUnit : (u : SIUnit) -> {auto ev : SIEven u} -> SIUnit
sqrtUnit (MkSIUnit xs) = MkSIUnit $ map div2 xs
  where
    div2 x = (sign x) * (toIntegerNat (natDiv2 $ toNat (abs x)))
      where
        sign x = if x < 0 then -1 else 1
        natDiv2 Z = Z
        natDiv2 (S Z) = Z
        natDiv2 (S (S n)) = 1 + (natDiv2 n)

infixr 7 *:
(*:) : SIUnit -> SIUnit -> SIUnit
(*:) (MkSIUnit xs) (MkSIUnit ys) = MkSIUnit $ zipWith (+) xs ys

infixr 7 /:
(/:) : SIUnit -> SIUnit -> SIUnit
(/:) (MkSIUnit xs) (MkSIUnit ys) = MkSIUnit $ zipWith (-) xs ys

infixr 8 ^:
(^:) : SIUnit -> Integer -> SIUnit
(^:) x n = if n < 0 then powUnit' (invUnit x) (toNat $ negate n)
           else powUnit' x (toNat n)
  where
    powUnit' x Z = zeroUnit
    powUnit' x (S n) = x *: (powUnit' x n)


showSIUnit : SIUnit -> String
showSIUnit (MkSIUnit [m, kg, s, a, k, cd, mol])
           = "m^" ++ (show m) ++ " "
           ++ "kg^" ++ (show kg) ++ " "
           ++ "s^" ++ (show s) ++ " "
           ++ "a^" ++ (show a) ++ " "
           ++ "k^" ++ (show k) ++ " "
           ++ "cd^" ++ (show cd) ++ " "
           ++ "mol^" ++ (show mol)

Show SIUnit where
  show u = showSIUnit u



-- * Base Units
Meter : SIUnit
Meter = MkSIUnit [1, 0, 0, 0, 0, 0, 0]

Kilogram : SIUnit
Kilogram = MkSIUnit [0, 1, 0, 0, 0, 0, 0]

Second : SIUnit
Second = MkSIUnit [0, 0, 1, 0, 0, 0, 0]

Ampere : SIUnit
Ampere = MkSIUnit [0, 0, 0, 1, 0, 0, 0]

Kelvin : SIUnit
Kelvin = MkSIUnit [0, 0, 0, 0, 1, 0, 0]

Candela : SIUnit
Candela = MkSIUnit [0, 0, 0, 0, 0, 1, 0]

Mole : SIUnit
Mole = MkSIUnit [0, 0, 0, 0, 0, 0, 1]


-- * Derived Units

Hertz : SIUnit
Hertz = invUnit Second

Radian : SIUnit
Radian = zeroUnit

Steradian : SIUnit
Steradian = zeroUnit

Newton : SIUnit
Newton = Kilogram *: Meter /: (Second ^: 2)

Pascal : SIUnit
Pascal = Newton /: (Meter ^: 2)

Joule : SIUnit
Joule = Newton *: Meter

Watt : SIUnit
Watt = Joule /: Second

Coulomb : SIUnit
Coulomb = Ampere *: Second

Volt : SIUnit
Volt = Watt /: Ampere

Farad : SIUnit
Farad = Coulomb /: Volt

Ohm : SIUnit
Ohm = Volt /: Ampere

Siemens : SIUnit
Siemens = invUnit Ohm

Weber : SIUnit
Weber = Volt *: Second

Tesla : SIUnit
Tesla = Weber /: (Meter ^: 2)

Henry : SIUnit
Henry = Weber /: Ampere

Lumen : SIUnit
Lumen = Candela *: Steradian

Lux : SIUnit
Lux = Lumen /: (Meter ^: 2)

Becquerel : SIUnit
Becquerel = invUnit Second

Gray : SIUnit
Gray = Joule /: Kilogram

Sievert : SIUnit
Sievert = Joule /: Kilogram

Katal : SIUnit
Katal = Mole /: Second
