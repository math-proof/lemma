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
public import Instance.Combinatorics.Enumerative.MeshPatternRStirling.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternRStirling.lean -/
section

namespace MetaMathlibExt

def meshWantedCount (k : ℕ) {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter (meshWantedMatch k σ)).card +
    (if meshWantedZero k σ then 1 else 0)

end MetaMathlibExt
end
