import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.PolyInitialExpansion
open MetaMathlibExt


/--
[chen_stirlingSecond_expansion](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PolyInitialExpansion.lean)
-/
@[path]
private lemma chen_stirlingSecond_expansion_eq
  {t : ℕ} :
-- imply
  ∀ (a : ℕ → ℕ → ℝ),
    (∀ (m s : ℕ),
    a m (s + 1) = (m : ℝ) * a m s - ((m : ℝ) + 1) * a (m + 1) s) →
    a 0 t = ∑ m ∈ Finset.range (t + 1),
    (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) *
    (Nat.stirlingSecond t m : ℝ) * a m 0 := by
-- proof
  apply MetaMathlibExt.chen_stirlingSecond_expansion t

/--
[poly_initial_expansion](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PolyInitialExpansion.lean)
-/
@[path]
private lemma poly_initial_expansion_eq
  :
-- imply
  ∀ (n : ℕ) (x : ℝ) (a : ℕ → ℕ → ℝ)
    (hrec : ∀ (m t : ℕ),
    a m (t + 1) = (m : ℝ) * a m t - ((m : ℝ) + 1) * a (m + 1) t),
    ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℝ) * x ^ k * a 0 (n - k) =
    ∑ m ∈ Finset.range (n + 1), (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) *
    (generalizedStirlingSecond n m x) * a m 0 := by
-- proof
  apply MetaMathlibExt.poly_initial_expansion


-- created on 2026-10-20
