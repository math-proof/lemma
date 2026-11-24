module
public import Mathlib.Data.Fintype.Perm
public import Def.Combinatorics.Enumerative.RStirlingFirstAlternatingExpansion
public import Theorem.Finset.Enumerative.RStirlingFirstAlternatingExpansion
public import Theorem.Finset.Enumerative.MeshPatternStirlingRecursion
public import Theorem.Combinatorics.Enumerative.MeshPatternStirlingRecursion.Part3
public import Theorem.Finset.Enumerative.MeshPatternGeneratingFunction
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternRStirling.lean -/
section

namespace MetaMathlibExt

def meshWantedMatch (k : ℕ) {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) : Prop :=
  (∀ h : Fin n, h < i → σ h < σ i) ∧
    k - 1 ≤ (Finset.univ.filter fun q : Fin n =>
      i < q ∧ (∀ m : Fin n, (∀ h : Fin n, σ h ≤ σ m) → q < m) ∧ σ i < σ q).card

end MetaMathlibExt
end
