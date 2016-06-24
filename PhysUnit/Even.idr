
module PhysUnit.Even


%access public export
%default total


||| Proposition that a natural number is even.
data EvenNat : Nat -> Type where
  ZEven : EvenNat Z
  SSEven : EvenNat n -> EvenNat (S (S n))

||| Proposition that an integer is even.
data Even : Integer -> Type where
  PrfEven : EvenNat (toNat (abs n)) -> Even n
