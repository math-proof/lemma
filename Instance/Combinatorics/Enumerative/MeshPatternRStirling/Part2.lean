/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternRStirling.lean -/

import Mathlib.Data.Fintype.Perm
import Def.Combinatorics.Enumerative.RStirlingFirstAlternatingExpansion
import Lemma.Finset.Enumerative.RStirlingFirstAlternatingExpansion
import Lemma.Finset.Enumerative.MeshPatternStirlingRecursion
import Theorem.Combinatorics.Enumerative.MeshPatternStirlingRecursion.Part3
import Lemma.Finset.Enumerative.MeshPatternGeneratingFunction
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.MeshPatternRStirling.Part2


section

namespace MetaMathlibExt

instance decMeshWantedZero (k : ℕ) {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Decidable (meshWantedZero k σ) := by
  unfold meshWantedZero
  infer_instance

end MetaMathlibExt
end
