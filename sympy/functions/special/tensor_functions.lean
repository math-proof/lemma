
def KroneckerDelta {α : Type} [DecidableEq α] (i j : α) : Nat :=
  Bool.toNat (i = j)

def relu [Zero α] [Max α] (x : α) : α :=
  max x 0
