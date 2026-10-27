import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.SpecialFunctions.Part1Ch8Entry14Qreflection

open Ramanujan.Part1Ch8.Entry14Qreflection

/--
[Part1Ch8Entry14Qreflection](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry14Qreflection.lean)
-/
@[path]
private lemma ramanujan_part1_ch8_entry14_qreflection_eq
-- given
  (x : ℝ)
  (hx0 : 0 ≤ x)
  (hx1 : x < 1) :
-- imply
  chapter8Entry14A 10 x = chapter8Entry14A10Closed x := by
-- proof
  apply Ramanujan.Part1Ch8.Entry14Qreflection.ramanujan_part1_ch8_entry14_qreflection x hx0 hx1

-- created on 2026-10-10
