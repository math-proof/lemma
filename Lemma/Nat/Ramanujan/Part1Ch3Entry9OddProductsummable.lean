import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry9OddProductsummable
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry9OddProductsummable


/--
[ramanujan_part1_ch3_entry9_odd_productsummable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry9OddProductsummable.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry9_odd_productsummable_eq
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
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry9OddProductsummable.ramanujan_part1_ch3_entry9_odd_productsummable a b x hb ε hεpos hεlt


-- created on 2026-10-20
