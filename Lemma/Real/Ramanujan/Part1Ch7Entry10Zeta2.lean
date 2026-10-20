import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch7Entry10Zeta2
open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory
open MathlibExt.Analysis.Ramanujan.Part1Ch7
open Entry10Zeta2


/--
[ramanujan_part1_ch7_entry10_zeta2](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry10Zeta2.lean)
-/
@[path]
private lemma ramanujan_part1_ch7_entry10_zeta2_eq
  {phi : ℂ → ℂ → ℂ}
  {n : ℕ}
  {x : ℂ}
-- given
  (hphi_meromorphic : ∀ x, MeromorphicOn (fun r : ℂ => phi r x) Set.univ)
  (hphi_series : ∀ r x, r.re < 0 → HasSum (chapter7PowerDifferenceTerm r x) (phi r x))
  (hn : 0 < n) :
-- imply
  MeromorphicOn (chapter7Entry10DistributionLeft phi n x) Set.univ ∧
    MeromorphicOn (chapter7Entry10ZetaSide n) Set.univ ∧
    chapter7Entry10DistributionLeft phi n x =ᶠ[codiscrete ℂ]
    chapter7Entry10ZetaSide n := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry10Zeta2.ramanujan_part1_ch7_entry10_zeta2 phi hphi_meromorphic hphi_series n hn x


-- created on 2026-10-20
