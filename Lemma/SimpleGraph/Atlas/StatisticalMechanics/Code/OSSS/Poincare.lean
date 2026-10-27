import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.OSSS.Poincare.Part2
open Finset StatMech StatMech.OSSS StatMech.OSSS.Poincare


/--
[eval_fullTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Poincare.lean)
-/
@[path]
private lemma eval_fullTree_eq
  [Fintype E]
  [DecidableEq E]
  {φ : ConfigSpace E → Bool}
  {l : List E}
  {ω : ConfigSpace E}
-- given
  (h : InsensOutside φ l) :
-- imply
  (fullTree φ l).eval ω = φ ω := by
-- proof
  apply StatMech.OSSS.Poincare.eval_fullTree φ l h ω

/--
[mem_queried_fullTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Poincare.lean)
-/
@[path]
private lemma mem_queried_fullTree_eq
  [Fintype E]
  [DecidableEq E]
  {e : E}
  {φ : ConfigSpace E → Bool}
  {l : List E}
  {ω : ConfigSpace E}
-- given
  (he : e ∈ l) :
-- imply
  e ∈ (fullTree φ l).queried ω := by
-- proof
  apply StatMech.OSSS.Poincare.mem_queried_fullTree e φ l he ω

/--
[eval_fullTreeUniv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Poincare.lean)
-/
@[path]
private lemma eval_fullTreeUniv_eq
  [Fintype E]
  [DecidableEq E]
  {φ : ConfigSpace E → Bool}
  {ω : ConfigSpace E} :
-- imply
  (fullTreeUniv φ).eval ω = φ ω := by
-- proof
  apply StatMech.OSSS.Poincare.eval_fullTreeUniv φ ω

/--
[evalR_fullTreeUniv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Poincare.lean)
-/
@[path]
private lemma evalR_fullTreeUniv_eq
  [Fintype E]
  [DecidableEq E]
  {φ : ConfigSpace E → Bool}
  {ω : ConfigSpace E} :
-- imply
  (fullTreeUniv φ).evalR ω = if φ ω then (1 : ℝ) else 0 := by
-- proof
  apply StatMech.OSSS.Poincare.evalR_fullTreeUniv φ ω

/--
[mem_queried_fullTreeUniv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Poincare.lean)
-/
@[path]
private lemma mem_queried_fullTreeUniv_eq
  [Fintype E]
  [DecidableEq E]
  {e : E}
  {φ : ConfigSpace E → Bool}
  {ω : ConfigSpace E} :
-- imply
  e ∈ (fullTreeUniv φ).queried ω := by
-- proof
  apply StatMech.OSSS.Poincare.mem_queried_fullTreeUniv e φ ω

/--
[reveal_fullTreeUniv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Poincare.lean)
-/
@[path]
private lemma reveal_fullTreeUniv_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {φ : ConfigSpace E → Bool}
  {e : E}
-- given
  (hν : IsProbWeight ν) :
-- imply
  reveal ν (fullTreeUniv φ) e = 1 := by
-- proof
  apply StatMech.OSSS.Poincare.reveal_fullTreeUniv hν φ e

/--
[poincare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Poincare.lean)
-/
@[path]
private lemma poincare_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {φ : ConfigSpace E → Bool}
-- given
  (hν : IsProbWeight ν) :
-- imply
  var ν (fun ω => if φ ω then (1 : ℝ) else 0) ≤ ∑ e, infl ν (fun ω => if φ ω then (1 : ℝ) else 0) e := by
-- proof
  apply StatMech.OSSS.Poincare.poincare hν φ

/--
[poincare_cov](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Poincare.lean)
-/
@[path]
private lemma poincare_cov_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {φ : ConfigSpace E → Bool}
  {g : ConfigSpace E → ℝ}
-- given
  (hν : IsProbWeight ν) :
-- imply
  cov ν (fun ω => if φ ω then (1 : ℝ) else 0) g ≤ ∑ e, infl ν g e := by
-- proof
  apply StatMech.OSSS.Poincare.poincare_cov hν φ g

/--
[poincare_bernoulli](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Poincare.lean)
-/
@[path]
private lemma poincare_bernoulli_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {φ : ConfigSpace E → Bool}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  var (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) ≤ ∑ e, infl (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e := by
-- proof
  apply StatMech.OSSS.Poincare.poincare_bernoulli hp0 hp1 φ


-- created on 2026-10-23
