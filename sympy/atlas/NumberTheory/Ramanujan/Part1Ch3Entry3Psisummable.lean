/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry3Psisummable.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import sympy.atlas.Analysis.SpecificLimits.RisingProductSeries
/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Entry 3

Summability of the factorial series `∑ (-1)ʲ xʲ⁺¹ / ((z+1)⋯(z+j+1))` in a sector
`|arg z| ≤ π - ε`, derived from `Complex.summable_neg_pow_mul_pow_div_prod_add_mul`.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry3Psisummable

/-- `ramanujan_part1_ch3_entry3_psisummable` without the hypotheses `x ≠ 0` and `ε < π`. It follows
from `Complex.summable_neg_pow_mul_pow_div_prod_add_mul` with `b = 1` and `c = z`: the upper sector
bound keeps `z` off the negative real axis, so no factor `z + (r + 1)` vanishes, and `R = 0`
works. -/
theorem ramanujan_part1_ch3_entry3_psisummable_general (x : ℂ) (ε : ℝ) (hε₁ : 0 < ε) :
    ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → -Real.pi + ε ≤ Complex.arg z → Complex.arg z ≤ Real.pi - ε →
      Summable (fun j : ℕ => (-1 : ℂ) ^ j * x ^ (j + 1) / ∏ k ∈ Finset.range (j + 1),
          (z + (↑(k + 1) : ℂ))) := by
  refine ⟨0, fun z _ _ h => ?_⟩
  have hs := Complex.summable_neg_pow_mul_pow_div_prod_add_mul (b := 1) (c := z) x fun r hr => by
    have hz : z = ((-((r : ℝ) + 1) : ℝ) : ℂ) := by
      push_cast at hr ⊢
      linear_combination hr
    rw [hz, Complex.arg_ofReal_of_neg (neg_neg_of_pos (by positivity))] at h
    linarith
  simpa only [one_mul] using hs

set_option linter.unusedVariables false in
/-- Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Entry 3, printed p. 47 / PDF p.
    57.
Proves `Wanted` entry `ramanujan_part1_ch3_entry3_psisummable`. It follows from
`ramanujan_part1_ch3_entry3_psisummable_general`; the hypotheses `x ≠ 0` and `ε < π` are unused
and keep the source's shape.
-/
@[nolint unusedArguments]
theorem ramanujan_part1_ch3_entry3_psisummable (x : ℂ)
    (hx : x ≠ 0) (ε : ℝ) (hε₁ : 0 < ε) (hε₂ : ε < Real.pi) :
    ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → -Real.pi + ε ≤ Complex.arg z → Complex.arg z ≤ Real.pi - ε →
      Summable (fun j : ℕ => (-1 : ℂ) ^ j * x ^ (j + 1) / ∏ k ∈ Finset.range (j + 1),
          (z + (↑(k + 1) : ℂ))) :=
  ramanujan_part1_ch3_entry3_psisummable_general x ε hε₁

end Entry3Psisummable

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
