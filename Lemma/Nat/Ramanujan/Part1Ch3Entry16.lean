import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry16
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry16


/--
[ramanujan_part1_ch3_entry16](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry16.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry16_eq
  {a x n : ℂ}
  {r : ℤ}
-- given
  (hx_ne : x ≠ 0)
  (hx_eq : x = a * Complex.log x)
  (ha : ‖a‖ > Real.exp 1 ∨ (a = (Real.exp 1 : ℂ) ∧ r ≤ -2))
  (hn : ∀ k : ℕ, r + (k : ℤ) < 0 → n + (k : ℂ) ≠ 0) :
-- imply
  n * varphi a x r n = varphi a x (r + 1) n - Complex.log x * varphi a x (r + 1) (n + 1) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry16.ramanujan_part1_ch3_entry16 a x n r hx_ne hx_eq ha hn


-- created on 2026-10-20
