import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Coding.HammingSpherePacking
open MathlibExt.Combinatorics.Coding.HammingSpherePacking


/--
[hamming_sphere_packing_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Coding/HammingSpherePacking.lean)
-/
@[path]
private lemma hamming_sphere_packing_bound_eq
  [Fintype α] [DecidableEq α]
  {n t : ℕ}
  {C : Finset (Fin n → α)}
-- given
  (hα : 2 ≤ Fintype.card α)
  (hDist : ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → 2 * t + 1 ≤ hammingDist c₁ c₂) :
-- imply
  C.card * (∑ i ∈ Finset.range (t + 1),
    n.choose i * (Fintype.card α - 1) ^ i) ≤ (Fintype.card α) ^ n := by
-- proof
  apply MathlibExt.Combinatorics.Coding.HammingSpherePacking.hamming_sphere_packing_bound C hα hDist


-- created on 2026-10-20
