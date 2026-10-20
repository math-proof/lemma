import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch7Entry20Generalizedbernoullisum
open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory
open MathlibExt.Analysis.Ramanujan.Part1Ch7
open Entry20Generalizedbernoullisum


/--
[ramanujan_part1_ch7_entry20_generalizedbernoullisum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry20Generalizedbernoullisum.lean)
-/
@[path]
private lemma ramanujan_part1_ch7_entry20_generalizedbernoullisum_eq
  :
-- imply
  MeromorphicOn chapter7Entry20Left Set.univ ∧
    MeromorphicOn chapter7Entry20Right Set.univ ∧
    chapter7Entry20Left =ᶠ[codiscrete ℂ] chapter7Entry20Right := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry20Generalizedbernoullisum.ramanujan_part1_ch7_entry20_generalizedbernoullisum


-- created on 2026-10-20
