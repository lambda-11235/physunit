
module PhysUnit.Even


%access public export
%default total


data EvenNat : Nat -> Type where
  ZEven : EvenNat Z
  SSEven : EvenNat n -> EvenNat (S (S n))

Even : Integer -> Type
Even n = EvenNat (toNat (abs n))
