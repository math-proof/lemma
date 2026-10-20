import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry4
open Entry9IiGeneralizedbellgeneratingDefining (generalizedBellGenerating)
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry4


/--
[ramanujan_part1_ch3_entry4](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry4.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry4_eq
  {a x : ℂ} :
-- imply
  HasSum (fun n : ℕ => a ^ n / (Nat.factorial n : ℂ) *
    (if n = 0 then (1 : ℂ) else generalizedBellGenerating 0 1 x (n - 1)))
    (Complex.exp (x * (Complex.exp a - 1))) ∧
    Summable (fun n : ℕ => ‖a ^ n / (Nat.factorial n : ℂ) *
    (if n = 0 then (1 : ℂ) else generalizedBellGenerating 0 1 x (n - 1))‖) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry4.ramanujan_part1_ch3_entry4 a x


-- created on 2026-10-20
