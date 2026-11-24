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
public import Instance.Combinatorics.Enumerative.MeshPatternRStirling


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternRStirling.lean -/
section

namespace MetaMathlibExt

def meshWantedZero (k : ℕ) {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  ∃ m : Fin n, (∀ h : Fin n, σ h ≤ σ m) ∧ k ≤ m.val + 1

end MetaMathlibExt
end
