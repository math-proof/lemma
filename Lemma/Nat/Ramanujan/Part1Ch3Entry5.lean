import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry5
open Entry9IiGeneralizedbellgeneratingDefining (generalizedBellGenerating)
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry5


/--
[ramanujan_part1_ch3_entry5](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry5.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry5_eq
  {n : ℕ}
  {x : ℂ} :
-- imply
  generalizedBellGenerating 0 1 x n = x *
    (Finset.range (n + 1)).sum (fun k => (Nat.choose n k : ℂ) *
    (if k = 0 then 1 else generalizedBellGenerating 0 1 x (k - 1))) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry5.ramanujan_part1_ch3_entry5 n x


-- created on 2026-10-20
