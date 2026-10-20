import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry12SummableSuccN
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry12SummableSuccN


/--
[ramanujan_part1_ch3_entry12_summable_succ_n_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry12SummableSuccN.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry12_summable_succ_n_general_eq
  {r : ℤ}
  {n a : ℂ}
-- given
  (ha : norm a > Real.exp 1 ∨ (a = ↑(Real.exp 1) ∧ r ≤ -2)) :
-- imply
  Summable (fun k : ℕ => norm ((n + (k : ℂ)) ^ (r + 1 + (k : ℤ)) / ((a ^ k) * (k.factorial : ℂ)))) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry12SummableSuccN.ramanujan_part1_ch3_entry12_summable_succ_n_general r n a ha

/--
[ramanujan_part1_ch3_entry12_summable_succ_n](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry12SummableSuccN.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry12_summable_succ_n_eq
  {r : ℤ}
  {n a : ℂ}
-- given
  (ha : norm a > Real.exp 1 ∨ (a = ↑(Real.exp 1) ∧ r ≤ -2))
  (hn : ∀ k : ℤ, 0 ≤ k → r + k < 0 → n + (k : ℂ) ≠ 0) :
-- imply
  Summable (fun k : ℕ => norm ((n + (k : ℂ)) ^ (r + 1 + (k : ℤ)) / ((a ^ k) * (k.factorial : ℂ)))) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry12SummableSuccN.ramanujan_part1_ch3_entry12_summable_succ_n r n a ha hn


-- created on 2026-10-20
