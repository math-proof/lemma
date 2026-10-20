import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Digits.ProdigiousCrtSolution
open MetaMathlibExt


/--
[exists_positive_crt_solution_nonzero_digit_product_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Digits/ProdigiousCrtSolution.lean)
-/
@[path]
private lemma exists_positive_crt_solution_nonzero_digit_product_one_eq
  {w b : ℕ}
  {r : Fin w → ℤ}
  {m : Fin w → ℕ}
-- given
  (hw : 0 < w)
  (hb : 3 ≤ b)
  (hmpos : ∀ v, 0 < m v)
  (hconsistent : ∃ x : ℤ, ∀ v, Int.ModEq (m v : ℤ) x (r v))
  (hzero : ∀ v, Nat.gcd (m v) b ≠ 1 → r v = 0) :
-- imply
  ∃ c : ℕ,
    0 < c ∧
    (∀ v, Int.ModEq (m v : ℤ) (c : ℤ) (r v)) ∧
    nonzeroDigitProd b c = 1 := by
-- proof
  apply MetaMathlibExt.exists_positive_crt_solution_nonzero_digit_product_one w b r m hw hb hmpos hconsistent hzero


-- created on 2026-10-20
