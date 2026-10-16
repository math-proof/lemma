def KroneckerDelta {α : Type _} [DecidableEq α] (i j : α) : Nat :=
  Bool.toNat (i = j)
