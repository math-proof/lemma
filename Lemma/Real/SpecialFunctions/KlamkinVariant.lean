import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.SpecialFunctions.KlamkinVariant
open MetaMathlibExt


/--
[variant_Klamkin](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/KlamkinVariant.lean)
-/
@[path]
private lemma variant_Klamkin_eq
  {a b : ℝ}
  {n : ℕ}
-- given
  (h_neg_a : ∀ m : ℕ, -a ≠ (m : ℝ))
  (h_neg_b : ∀ m : ℕ, -b ≠ (m : ℝ))
  (h_n_pos : 1 ≤ n)
  (h_n_bound : (n : ℝ) < -a - 1)
  (h_ab : ∀ m : ℤ, a - b ≠ (m : ℝ)) :
-- imply
  HasSum (fun k : ℕ => (-1 : ℝ) ^ k * (Nat.choose (n + k - 1) k : ℝ) *
    (Real.Gamma (a + 1) /
    (Real.Gamma (b + (k : ℝ) + 1) *
    Real.Gamma (a - (b + (k : ℝ)) + 1)))⁻¹)
    ((a + 1) / (a + (n : ℝ) + 1) *
    ((Real.Gamma (a + (n : ℝ) + 1) /
    (Real.Gamma (b + 1) * Real.Gamma (a + (n : ℝ) - b + 1)))⁻¹)) := by
-- proof
  apply MetaMathlibExt.variant_Klamkin a b n h_neg_a h_neg_b h_n_pos h_n_bound h_ab


-- created on 2026-10-20
