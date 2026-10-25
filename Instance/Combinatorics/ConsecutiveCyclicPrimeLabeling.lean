/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/ConsecutiveCyclicPrimeLabeling.lean -/

import Mathlib.Data.Nat.GCD.Basic
import Def.Combinatorics.ConsecutiveCyclicPrimeLabeling


namespace MetaMathlibExt

instance decidableLadderAdj (n : ℕ) (i j : Fin (2 * n)) :
    Decidable (LadderAdj n i j) := by
  unfold LadderAdj
  infer_instance

end MetaMathlibExt
