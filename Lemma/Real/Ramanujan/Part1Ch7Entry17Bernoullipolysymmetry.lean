import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch7Entry17Bernoullipolysymmetry
open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory
open DirichletBeta
open MathlibExt.Analysis.Ramanujan.Part1Ch7
open Entry17Bernoullipolysymmetry


/--
[ramanujan_part1_ch7_entry17_bernoullipolysymmetry](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry17Bernoullipolysymmetry.lean)
-/
@[path]
private lemma ramanujan_part1_ch7_entry17_bernoullipolysymmetry_eq
  :
-- imply
  Differentiable ℂ chapter7DirichletBeta ∧
    (∀ s : ℂ, 0 < s.re →
    Tendsto (chapter7DirichletBetaPartialSum s) atTop
    (𝓝 (chapter7DirichletBeta s))) ∧
    MeromorphicOn chapter7EulerStar Set.univ ∧
    MeromorphicOn chapter7Entry17Left Set.univ ∧
    MeromorphicOn chapter7Entry17Right Set.univ ∧
    chapter7Entry17Left =ᶠ[codiscrete ℂ] chapter7Entry17Right := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry17Bernoullipolysymmetry.ramanujan_part1_ch7_entry17_bernoullipolysymmetry


-- created on 2026-10-20
