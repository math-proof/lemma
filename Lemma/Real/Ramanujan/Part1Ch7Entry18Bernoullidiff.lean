import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch7Entry18Bernoullidiff
open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory
open DirichletBeta
open MathlibExt.Analysis.Ramanujan.Part1Ch7
open Entry18Bernoullidiff


/--
[ramanujan_part1_ch7_entry18_bernoullidiff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry18Bernoullidiff.lean)
-/
@[path]
private lemma ramanujan_part1_ch7_entry18_bernoullidiff_eq
  :
-- imply
  MeromorphicOn chapter7Entry18Left Set.univ ∧
    MeromorphicOn chapter7Entry18Right Set.univ ∧
    MeromorphicOn chapter7Entry18FunctionalRight Set.univ ∧
    chapter7Entry18Left =ᶠ[codiscrete ℂ] chapter7Entry18Middle ∧
    chapter7Entry18Middle =ᶠ[codiscrete ℂ] chapter7Entry18Right ∧
    chapter7DirichletBeta =ᶠ[codiscrete ℂ]
    chapter7Entry18FunctionalRight := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry18Bernoullidiff.ramanujan_part1_ch7_entry18_bernoullidiff


-- created on 2026-10-20
