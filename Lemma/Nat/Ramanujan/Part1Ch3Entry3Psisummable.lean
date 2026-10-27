import Mathlib
import Initialize.Tactic.Attr.Basic
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3


namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry3Psisummable

/--
[ramanujan_part1_ch3_entry3_psisummable_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry3Psisummable.lean)
-/
@[path]
lemma ramanujan_part1_ch3_entry3_psisummable_general
  {x : ℂ}
  {ε : ℝ}
-- given
  (hε₁ : 0 < ε) :
-- imply
  ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → -Real.pi + ε ≤ Complex.arg z → Complex.arg z ≤ Real.pi - ε →
    Summable (fun j : ℕ => (-1 : ℂ) ^ j * x ^ (j + 1) / ∏ k ∈ Finset.range (j + 1),
    (z + (↑(k + 1) : ℂ))) := by
-- proof
  refine ⟨0, fun z _ _ h => ?_⟩
  have hs := Complex.summable_neg_pow_mul_pow_div_prod_add_mul (b := 1) (c := z) x fun r hr => by
    have hz : z = ((-((r : ℝ) + 1) : ℝ) : ℂ) := by
      push_cast at hr ⊢
      linear_combination hr
    rw [hz, Complex.arg_ofReal_of_neg (neg_neg_of_pos (by positivity))] at h
    linarith
  simpa only [one_mul] using hs
set_option linter.unusedVariables false in

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry3Psisummable

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry3Psisummable

/--
[ramanujan_part1_ch3_entry3_psisummable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry3Psisummable.lean)
-/
@[path]
lemma ramanujan_part1_ch3_entry3_psisummable
  {x : ℂ}
  {ε : ℝ}
-- given
  (hx : x ≠ 0)
  (hε₁ : 0 < ε)
  (hε₂ : ε < Real.pi) :
-- imply
  ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → -Real.pi + ε ≤ Complex.arg z → Complex.arg z ≤ Real.pi - ε →
    Summable (fun j : ℕ => (-1 : ℂ) ^ j * x ^ (j + 1) / ∏ k ∈ Finset.range (j + 1),
    (z + (↑(k + 1) : ℂ))) :=
-- proof
  ramanujan_part1_ch3_entry3_psisummable_general x ε hε₁

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry3Psisummable


-- created on 2026-10-20
-- updated on 2026-10-26
