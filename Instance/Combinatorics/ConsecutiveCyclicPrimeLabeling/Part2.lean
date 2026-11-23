/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/ConsecutiveCyclicPrimeLabeling.lean -/

module

public import Mathlib.Data.Nat.GCD.Basic
public import Def.Combinatorics.ConsecutiveCyclicPrimeLabeling.Part2
@[expose] public section

namespace MetaMathlibExt

instance decidableIsConsecutiveCyclicPrimeLabeling (n offset : ℕ) :
    Decidable (IsConsecutiveCyclicPrimeLabeling n offset) := by
  unfold IsConsecutiveCyclicPrimeLabeling LadderAdj Nat.Coprime
  infer_instance

end MetaMathlibExt
