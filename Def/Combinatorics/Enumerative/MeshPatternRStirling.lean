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


section

namespace MetaMathlibExt

def meshWantedMatch (k : ℕ) {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) : Prop :=
  (∀ h : Fin n, h < i → σ h < σ i) ∧
    k - 1 ≤ (Finset.univ.filter fun q : Fin n =>
      i < q ∧ (∀ m : Fin n, (∀ h : Fin n, σ h ≤ σ m) → q < m) ∧ σ i < σ q).card

end MetaMathlibExt
end
