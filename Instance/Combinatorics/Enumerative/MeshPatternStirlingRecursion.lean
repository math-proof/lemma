/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternStirlingRecursion.lean -/

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.MeshPatternStirlingRecursion


section

namespace MetaMathlibExt

instance decMatchPred (m : ℕ) (r : ℕ) (σ : Equiv.Perm (Fin m)) :
    DecidablePred (MatchPred r σ) := by
  intro i
  unfold MatchPred
  infer_instance

instance decZeroPred (m : ℕ) (r : ℕ) (σ : Equiv.Perm (Fin m)) :
    Decidable (ZeroPred r σ) := by
  unfold ZeroPred
  infer_instance

end MetaMathlibExt
end
