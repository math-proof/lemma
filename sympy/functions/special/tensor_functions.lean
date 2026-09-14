
def KroneckerDelta {α : Type} [DecidableEq α] (i j : α) : Nat :=
  Bool.toNat (i = j)
