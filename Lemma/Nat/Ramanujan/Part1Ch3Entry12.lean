import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry12
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry12


/--
[ramanujan_part1_ch3_entry12](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry12.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry12_eq
  {r : ℤ}
  {n a : ℂ}
-- given
  (ha : ‖a‖ > Real.exp 1 ∨ (a = (Real.exp 1 : ℂ) ∧ r ≤ -2))
  (hn : ∀ k : ℕ, r + (k : ℤ) < 0 → n + (k : ℂ) ≠ 0) :
-- imply
  F (r + 1) n a = n * F r n a + (1 / a) * F (r + 1) (n + 1) a := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry12.ramanujan_part1_ch3_entry12 r n a ha hn


-- created on 2026-10-20
