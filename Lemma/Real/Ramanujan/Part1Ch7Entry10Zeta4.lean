import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch7Entry10Zeta4
open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory
open MathlibExt.Analysis.Ramanujan.Part1Ch7
open Entry10Zeta4


/--
[ramanujan_part1_ch7_entry10_zeta4](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry10Zeta4.lean)
-/
@[path]
private lemma ramanujan_part1_ch7_entry10_zeta4_eq
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  MeromorphicOn (chapter7Entry10ZetaSide n) Set.univ ∧
    MeromorphicOn (chapter7Entry10BernoulliSide n) Set.univ ∧
    chapter7Entry10ZetaSide n =ᶠ[codiscrete ℂ]
    chapter7Entry10BernoulliSide n := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry10Zeta4.ramanujan_part1_ch7_entry10_zeta4 n hn


-- created on 2026-10-20
