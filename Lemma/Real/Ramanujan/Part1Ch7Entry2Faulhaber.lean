import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch7Entry2Faulhaber
open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory
open MathlibExt.Analysis.Ramanujan.Part1Ch7
open Entry2Faulhaber


/--
[ramanujan_part1_ch7_entry2_faulhaber](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry2Faulhaber.lean)
-/
@[path]
private lemma ramanujan_part1_ch7_entry2_faulhaber_eq
  :
-- imply
  (∀ s : ℂ, 0 < s.re →
    Tendsto (chapter7EtaPartialSum s) atTop (𝓝 (chapter7Eta s))) ∧
    MeromorphicOn (fun r : ℂ => chapter7Eta (-r)) Set.univ ∧
    MeromorphicOn chapter7Entry2Value Set.univ ∧
    (fun r : ℂ => chapter7Eta (-r)) =ᶠ[codiscrete ℂ] chapter7Entry2Value := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry2Faulhaber.ramanujan_part1_ch7_entry2_faulhaber


-- created on 2026-10-20
