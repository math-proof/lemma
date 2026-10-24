import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.Z2GaugeIsingAdapter
open Finset StatMech StatMech.FrontierA


/--
[dualIsingCoupling_dualEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeIsingAdapter.lean)
-/
@[path]
private lemma dualIsingCoupling_dualEdge_eq
  [Fintype E]
  [DecidableEq E]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {dualEdge : P ≃ G.edgeFinset}
  {K : P → ℝ}
  {p : P} :
-- imply
  dualIsingCoupling dualEdge K (dualEdge p).1 = gaugeDualCoupling (K p) := by
-- proof
  apply StatMech.FrontierA.dualIsingCoupling_dualEdge dualEdge K p

/--
[sum_coupling_bond_eq_sub_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeIsingAdapter.lean)
-/
@[path]
private lemma sum_coupling_bond_eq_sub_cut_eq
  [Fintype E]
  [DecidableEq E]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {s : ConfigSpace V} :
-- imply
  (∑ e ∈ G.edgeFinset, J e * bond s e) = (∑ e ∈ G.edgeFinset, J e) - 2 * ∑ e ∈ cutEdges G s, J e := by
-- proof
  apply StatMech.FrontierA.sum_coupling_bond_eq_sub_cut J s

/--
[wJ_eq_domainWallActivity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeIsingAdapter.lean)
-/
@[path]
private lemma wJ_eq_domainWallActivity_eq
  [Fintype E]
  [DecidableEq E]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {s : ConfigSpace V} :
-- imply
  wJ G.edgeFinset J (fun _ => 0) s = Real.exp (∑ e ∈ G.edgeFinset, J e) * ∏ e ∈ cutEdges G s, Real.exp (-2 * J e) := by
-- proof
  apply StatMech.FrontierA.wJ_eq_domainWallActivity J s

/--
[ZJ_eq_domainWallSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeIsingAdapter.lean)
-/
@[path]
private lemma ZJ_eq_domainWallSum_eq
  [Fintype E]
  [DecidableEq E]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ} :
-- imply
  ZJ G.edgeFinset J (fun _ => 0) = Real.exp (∑ e ∈ G.edgeFinset, J e) * ∑ s : ConfigSpace V, ∏ e ∈ cutEdges G s, Real.exp (-2 * J e) := by
-- proof
  apply StatMech.FrontierA.ZJ_eq_domainWallSum J

/--
[weightedCutSum_eq_two_mul_cutSpace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeIsingAdapter.lean)
-/
@[path]
private lemma weightedCutSum_eq_two_mul_cutSpace_eq
  [Fintype E]
  [DecidableEq E]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Nonempty V]
  {w : Sym2 V → ℝ}
-- given
  (hG : G.Preconnected) :
-- imply
  (∑ s : ConfigSpace V, ∏ e ∈ cutEdges G s, w e) = 2 * ∑ delta ∈ cutSpace G, ∏ e ∈ delta, w e := by
-- proof
  apply StatMech.FrontierA.weightedCutSum_eq_two_mul_cutSpace hG w

/--
[gaugeClosedSurfaceSum_eq_dualCutSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeIsingAdapter.lean)
-/
@[path]
private lemma gaugeClosedSurfaceSum_eq_dualCutSum_eq
  [Fintype E]
  [DecidableEq E]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {incidence : P → Finset E}
  {K : P → ℝ}
  {dualEdge : P ≃ G.edgeFinset}
-- given
  (hK : ∀ p, 0 < K p)
  (surfaceEquiv : {A : Finset P // A ∈ gaugeClosedSurfaceFamily incidence} ≃ {delta : Finset (Sym2 V) // delta ∈ cutSpace G})
  (hmap : ∀ A, (surfaceEquiv A).1 = A.1.map (dualPlaquetteEmbedding dualEdge)) :
-- imply
  gaugeClosedSurfaceSum incidence K = ∑ delta ∈ cutSpace G, ∏ e ∈ delta, Real.exp (-2 * dualIsingCoupling dualEdge K e) := by
-- proof
  apply StatMech.FrontierA.gaugeClosedSurfaceSum_eq_dualCutSum incidence K hK dualEdge surfaceEquiv hmap

/--
[gaugeWilsonSurfaceSum_eq_shiftedDualCutSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeIsingAdapter.lean)
-/
@[path]
private lemma gaugeWilsonSurfaceSum_eq_shiftedDualCutSum_eq
  [Fintype E]
  [DecidableEq E]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {incidence : P → Finset E}
  {K : P → ℝ}
  {L : Finset E}
  {D : Finset (Sym2 V)}
  {dualEdge : P ≃ G.edgeFinset}
-- given
  (hK : ∀ p, 0 < K p)
  (surfaceEquiv : {A : Finset P // A ∈ gaugeWilsonSurfaceFamily incidence L} ≃ {gamma : Finset (Sym2 V) // gamma ∈ shiftedDualCutFamily (G := G) D})
  (hmap : ∀ A, (surfaceEquiv A).1 = A.1.map (dualPlaquetteEmbedding dualEdge)) :
-- imply
  gaugeWilsonSurfaceSum incidence K L = ∑ gamma ∈ shiftedDualCutFamily (G := G) D, ∏ e ∈ gamma, Real.exp (-2 * dualIsingCoupling dualEdge K e) := by
-- proof
  apply StatMech.FrontierA.gaugeWilsonSurfaceSum_eq_shiftedDualCutSum incidence K hK L D dualEdge surfaceEquiv hmap

/--
[gaugeWilsonExpectation_eq_dualDisorderRatio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeIsingAdapter.lean)
-/
@[path]
private lemma gaugeWilsonExpectation_eq_dualDisorderRatio_eq
  [Fintype E]
  [DecidableEq E]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {incidence : P → Finset E}
  {K : P → ℝ}
  {L : Finset E}
  {D : Finset (Sym2 V)}
  {dualEdge : P ≃ G.edgeFinset}
-- given
  (hK : ∀ p, 0 < K p)
  (closedEquiv : {A : Finset P // A ∈ gaugeClosedSurfaceFamily incidence} ≃ {delta : Finset (Sym2 V) // delta ∈ cutSpace G})
  (hclosed : ∀ A, (closedEquiv A).1 = A.1.map (dualPlaquetteEmbedding dualEdge))
  (wilsonEquiv : {A : Finset P // A ∈ gaugeWilsonSurfaceFamily incidence L} ≃ {gamma : Finset (Sym2 V) // gamma ∈ shiftedDualCutFamily (G := G) D})
  (hwilson : ∀ A, (wilsonEquiv A).1 = A.1.map (dualPlaquetteEmbedding dualEdge)) :
-- imply
  gaugeWilsonExpectation incidence K L = (∑ gamma ∈ shiftedDualCutFamily (G := G) D, ∏ e ∈ gamma, Real.exp (-2 * dualIsingCoupling dualEdge K e)) / (∑ delta ∈ cutSpace G, ∏ e ∈ delta, Real.exp (-2 * dualIsingCoupling dualEdge K e)) := by
-- proof
  apply StatMech.FrontierA.gaugeWilsonExpectation_eq_dualDisorderRatio incidence K hK L D dualEdge closedEquiv hclosed wilsonEquiv hwilson

/--
[gaugePartition_isingDuality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeIsingAdapter.lean)
-/
@[path]
private lemma gaugePartition_isingDuality_eq
  [Fintype E]
  [DecidableEq E]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Nonempty V]
  {incidence : P → Finset E}
  {K : P → ℝ}
  {dualEdge : P ≃ G.edgeFinset}
-- given
  (hG : G.Preconnected)
  (hK : ∀ p, 0 < K p)
  (surfaceEquiv : {A : Finset P // A ∈ gaugeClosedSurfaceFamily incidence} ≃ {delta : Finset (Sym2 V) // delta ∈ cutSpace G})
  (hmap : ∀ A, (surfaceEquiv A).1 = A.1.map (dualPlaquetteEmbedding dualEdge)) :
-- imply
  (Real.exp (∑ e ∈ G.edgeFinset, dualIsingCoupling dualEdge K e) * 2) * gaugePartition incidence K = ((2 : ℝ) ^ Fintype.card E * ∏ p : P, Real.cosh (K p)) * ZJ G.edgeFinset (dualIsingCoupling dualEdge K) (fun _ => 0) := by
-- proof
  apply StatMech.FrontierA.gaugePartition_isingDuality hG incidence K hK dualEdge surfaceEquiv hmap


-- created on 2026-10-23
