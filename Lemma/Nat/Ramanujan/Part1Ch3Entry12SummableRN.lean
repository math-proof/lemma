import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry12SummableRN
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry12SummableRN


/--
[ramanujan_part1_ch3_entry12_summable_r_n](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry12SummableRN.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry12_summable_r_n_eq
  {r : ℤ}
  {n a : ℂ}
-- given
  (ha : ‖a‖ > Real.exp 1 ∨ (a = (Real.exp 1 : ℂ) ∧ r ≤ -2))
  (hn : ∀ k : ℕ, r + (k : ℤ) < 0 → n + (k : ℂ) ≠ 0) :
-- imply
  Summable (fun k : ℕ => ‖(n + (k : ℂ)) ^ (r + (k : ℤ)) / (a ^ k * (Nat.factorial k : ℂ))‖) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry12SummableRN.ramanujan_part1_ch3_entry12_summable_r_n r n a ha hn


-- created on 2026-10-20
