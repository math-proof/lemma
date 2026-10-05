import Mathlib
import sympy.Basic


/--
[exists_isIdempotentElem_mul_eq_of_mul_eq_zero_of_isCoprime](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_exists_isIdempotentElem_mul_eq_of_mul_eq_zero_of_isCoprime.lean)
-/
@[main]
private lemma main
  {R : Type u} [CommRing R]
  {f g : R}
-- given
  (hfg : f * g = 0)
  (hcop : IsCoprime f g) :
-- imply
  ∃ e w : R, IsIdempotentElem e ∧ IsUnit w ∧ f = e * w := by
-- proof
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : f * (u * f) = f := by linear_combination (-v) * hfg + f * huv
  refine ⟨u * f, f + (1 - u * f), ?_, ?_, ?_⟩
  · show u * f * (u * f) = u * f
    linear_combination (-(u * v)) * hfg + (u * f) * huv
  · exact isUnit_iff_exists_inv.mpr ⟨u * (u * f) + (1 - u * f), by linear_combination (2 * u - u ^ 2 - 1) * h1⟩
  · linear_combination (u - 1) * h1


-- created on 2026-10-05
