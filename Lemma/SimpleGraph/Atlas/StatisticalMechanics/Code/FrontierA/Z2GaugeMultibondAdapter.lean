import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeMultibondAdapter.Part2
open Finset StatMech StatMech.FrontierA


/--
[mem_multibondCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeMultibondAdapter.lean)
-/
@[path]
private lemma mem_multibondCut_eq
  [Fintype E]
  [DecidableEq E]
  {ends : P → V × V}
  {s : V → Bool}
  {p : P} :
-- imply
  p ∈ multibondCut ends s ↔ s (ends p).1 ≠ s (ends p).2 := by
-- proof
  apply StatMech.FrontierA.mem_multibondCut ends s p

/--
[multibond_energy_eq_sub_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeMultibondAdapter.lean)
-/
@[path]
private lemma multibond_energy_eq_sub_cut_eq
  [Fintype E]
  [DecidableEq E]
  {ends : P → V × V}
  {J : P → Real}
  {s : V → Bool} :
-- imply
  (∑ p : P, J p * if s (ends p).1 = s (ends p).2 then 1 else -1) = (∑ p : P, J p) - 2 * ∑ p ∈ multibondCut ends s, J p := by
-- proof
  apply StatMech.FrontierA.multibond_energy_eq_sub_cut ends J s

/--
[multibondIsingWeight_eq_activity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeMultibondAdapter.lean)
-/
@[path]
private lemma multibondIsingWeight_eq_activity_eq
  [Fintype E]
  [DecidableEq E]
  {ends : P → V × V}
  {J : P → Real}
  {s : V → Bool} :
-- imply
  multibondIsingWeight ends J s = Real.exp (∑ p : P, J p) * ∏ p ∈ multibondCut ends s, Real.exp (-2 * J p) := by
-- proof
  apply StatMech.FrontierA.multibondIsingWeight_eq_activity ends J s

/--
[multibondCut_unanchorConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeMultibondAdapter.lean)
-/
@[path]
private lemma multibondCut_unanchorConfig_eq
  [Fintype E]
  [DecidableEq E]
  {ends : P → V × V}
  {root : V}
  {b : Bool}
  {s : AnchoredConfig V root} :
-- imply
  multibondCut ends (unanchorConfig b s) = multibondCut ends s.1 := by
-- proof
  apply StatMech.FrontierA.multibondCut_unanchorConfig ends root b s

/--
[multibondIsingPartition_eq_two_mul_anchored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeMultibondAdapter.lean)
-/
@[path]
private lemma multibondIsingPartition_eq_two_mul_anchored_eq
  [Fintype E]
  [DecidableEq E]
  {ends : P → V × V}
  {J : P → Real}
  {root : V} :
-- imply
  multibondIsingPartition ends J = 2 * ∑ s : AnchoredConfig V root, Real.exp (∑ p : P, J p) * ∏ p ∈ multibondCut ends s.1, Real.exp (-2 * J p) := by
-- proof
  apply StatMech.FrontierA.multibondIsingPartition_eq_two_mul_anchored ends J root

/--
[gaugePartition_multibondIsingDuality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeMultibondAdapter.lean)
-/
@[path]
private lemma gaugePartition_multibondIsingDuality_eq
  [Fintype E]
  [DecidableEq E]
  {incidence : P → Finset E}
  {K : P → Real}
  {root : V}
  {ends : P → V × V}
-- given
  (hK : ∀ p, 0 < K p)
  (surfaceEquiv : {A : Finset P // A ∈ gaugeClosedSurfaceFamily incidence} ≃ AnchoredConfig V root)
  (hmap : ∀ A, multibondCut ends (surfaceEquiv A).1 = A.1) :
-- imply
  (Real.exp (∑ p : P, gaugeDualCoupling (K p)) * 2) * gaugePartition incidence K = ((2 : Real) ^ Fintype.card E * ∏ p : P, Real.cosh (K p)) * multibondIsingPartition ends (fun p => gaugeDualCoupling (K p)) := by
-- proof
  apply StatMech.FrontierA.gaugePartition_multibondIsingDuality incidence K hK root ends surfaceEquiv hmap

/--
[gaugeWilsonExpectation_eq_multibondDisorderRatio_of_sheet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeMultibondAdapter.lean)
-/
@[path]
private lemma gaugeWilsonExpectation_eq_multibondDisorderRatio_of_sheet_eq
  [Fintype E]
  [DecidableEq E]
  {incidence : P → Finset E}
  {K : P → Real}
  {L : Finset E}
  {D : Finset P}
  {root : V}
  {ends : P → V × V}
-- given
  (hK : ∀ p, 0 < K p)
  (hD : HasWilsonBoundary incidence D L)
  (surfaceEquiv : {A : Finset P // A ∈ gaugeClosedSurfaceFamily incidence} ≃ AnchoredConfig V root)
  (hmap : ∀ A, multibondCut ends (surfaceEquiv A).1 = A.1) :
-- imply
  gaugeWilsonExpectation incidence K L = (∑ s : AnchoredConfig V root, ∏ p ∈ multibondCut ends s.1 ∆ D, Real.exp (-2 * gaugeDualCoupling (K p))) / (∑ s : AnchoredConfig V root, ∏ p ∈ multibondCut ends s.1, Real.exp (-2 * gaugeDualCoupling (K p))) := by
-- proof
  apply StatMech.FrontierA.gaugeWilsonExpectation_eq_multibondDisorderRatio_of_sheet incidence K hK L D hD root ends surfaceEquiv hmap


-- created on 2026-10-23
