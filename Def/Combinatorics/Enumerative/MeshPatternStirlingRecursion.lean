/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternStirlingRecursion.lean -/

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring


section

namespace MetaMathlibExt

/-! # Stirling-type recursion for mesh-pattern counts -/

/-- Canonical mesh-match predicate: position `i` is a left-to-right maximum of `σ` with at
least `r - 1` larger entries strictly between `i` and a global maximizer. Shared by the
recursion (`meshPatternCount_stirlingRecursion`) and the coefficient theorem
(`meshPatternCount_eq_factorial_mul_rStirlingNumber`). -/
def MatchPred {m : ℕ} (r : ℕ) (σ : Equiv.Perm (Fin m)) (i : Fin m) : Prop :=
  ∃ maxIndex : Fin m,
    (∀ t : Fin m, σ t ≤ σ maxIndex) ∧
    r - 1 ≤ (Finset.univ.filter fun t : Fin m =>
      i < t ∧ t < maxIndex ∧ σ i < σ t).card ∧
    ∀ t : Fin m, t < i → σ t < σ i

/-- Canonical zero-match predicate: some global maximizer of `σ` sits at position `≥ r`.
Shared by the recursion and the coefficient theorem. -/
def ZeroPred {m : ℕ} (r : ℕ) (σ : Equiv.Perm (Fin m)) : Prop :=
  ∃ maxIndex : Fin m,
    (∀ t : Fin m, σ t ≤ σ maxIndex) ∧ r ≤ maxIndex.val + 1

end MetaMathlibExt
end
