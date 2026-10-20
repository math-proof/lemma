import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry9IiGeneralizedbellgenerating
open Entry9IiGeneralizedbellgeneratingDefining (generalizedBellGenerating)
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry9IiGeneralizedbellgenerating


/--
[ramanujan_part1_ch3_entry9_ii_generalizedbellgenerating](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry9IiGeneralizedbellgenerating.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry9_ii_generalizedbellgenerating_eq
  {a b x y : ℂ} :
-- imply
  HasSum (fun n : ℕ => y ^ n / (Nat.factorial n : ℂ) * generalizedBellGenerating a b x n)
    (x * Complex.exp ((a + b) * y) * Complex.exp (x * (Complex.exp (b * y) - 1))) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry9IiGeneralizedbellgenerating.ramanujan_part1_ch3_entry9_ii_generalizedbellgenerating a b x y


-- created on 2026-10-20
