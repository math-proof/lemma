/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/ConsecutiveCyclicPrimeLabeling.lean -/

import Mathlib.Data.Nat.GCD.Basic
import Def.Combinatorics.ConsecutiveCyclicPrimeLabeling.Part2


namespace MetaMathlibExt

instance decidableIsConsecutiveCyclicPrimeLabeling (n offset : ℕ) :
    Decidable (IsConsecutiveCyclicPrimeLabeling n offset) := by
  unfold IsConsecutiveCyclicPrimeLabeling LadderAdj Nat.Coprime
  infer_instance

end MetaMathlibExt
