import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry9IiGeneralizedbellgeneratingDefining
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry9IiGeneralizedbellgeneratingDefining


/--
[ramanujan_part1_ch3_entry9_ii_generalizedbellgenerating_defining](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry9IiGeneralizedbellgeneratingDefining.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry9_ii_generalizedbellgenerating_defining_eq
  {a b x : ℂ}
  {n : ℕ} :
-- imply
  HasSum (fun k : ℕ => (a + b * (↑(k + 1) : ℂ)) ^ n * x ^ (k + 1) / (↑(Nat.factorial k) : ℂ))
    (Complex.exp x * generalizedBellGenerating a b x n) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry9IiGeneralizedbellgeneratingDefining.ramanujan_part1_ch3_entry9_ii_generalizedbellgenerating_defining a b x n


-- created on 2026-10-20
