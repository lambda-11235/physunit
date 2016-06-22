
module PhysUnit.Even


%access public export
%default total


data EvenNat : Nat -> Type where
  ZEven : EvenNat Z
  SSEven : EvenNat n -> EvenNat (S (S n))

data Even : Integer -> Type where
  PrfEven : EvenNat (toNat (abs n)) -> Even n
