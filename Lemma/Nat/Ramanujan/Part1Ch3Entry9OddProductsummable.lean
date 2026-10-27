import Mathlib
import Initialize.Tactic.Attr.Basic
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3


namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry9OddProductsummable

/--
[ramanujan_part1_ch3_entry9_odd_productsummable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry9OddProductsummable.lean)
-/
@[path]
lemma ramanujan_part1_ch3_entry9_odd_productsummable
  {a b x : ℂ}
  {ε : ℝ}
-- given
  (hb : b ≠ 0)
  (hεpos : 0 < ε)
  (hεlt : ε < Real.pi) :
-- imply
  ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖(z + a) / b‖ → -Real.pi + ε ≤ Complex.arg ((z + a) / b) →
    Complex.arg ((z + a) / b) ≤ Real.pi - ε →
    Summable (fun j : ℕ =>
    ((-b) ^ j * x ^ (j + 1) / ∏ r ∈ Finset.range (j + 1),
    (z + a + b * ((r + 1 : ℕ) : ℂ)))) := by
-- proof
  refine ⟨0, fun z _ _ h => Complex.summable_neg_pow_mul_pow_div_prod_add_mul x fun r hr => ?_⟩
  have hw : (z + a) / b = ((-((r : ℝ) + 1) : ℝ) : ℂ) := by
    rw [div_eq_iff hb]
    push_cast at hr ⊢
    linear_combination hr
  rw [hw, Complex.arg_ofReal_of_neg (neg_neg_of_pos (by positivity))] at h
  linarith

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry9OddProductsummable


-- created on 2026-10-20
-- updated on 2026-10-26
