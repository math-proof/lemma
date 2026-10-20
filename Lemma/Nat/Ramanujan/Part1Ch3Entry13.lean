import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry13
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry13


/--
[ramanujan_part1_ch3_entry13](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry13.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry13_eq
  {a : ℝ}
-- given
  (ha : |a| ≥ Real.exp 1) :
-- imply
  ∃ x : ℝ, 0 < x ∧ x = a * Real.log x ∧ ∀ n : ℝ,
    HasSum (fun k : ℕ => if k = 0 then (1 : ℝ) else n * (n + (k : ℝ)) ^ (k - 1) /
    (a ^ k * (Nat.factorial k : ℝ))) (x ^ n) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry13.ramanujan_part1_ch3_entry13 a ha


-- created on 2026-10-20
