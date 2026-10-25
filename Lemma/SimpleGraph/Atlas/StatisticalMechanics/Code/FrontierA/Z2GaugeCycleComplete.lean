import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCycleComplete.Part8
open Finset SimpleGraph StatMech StatMech.FrontierA


/--
[mem_gaugeToggle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCycleComplete.lean)
-/
@[path]
private lemma mem_gaugeToggle_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq alpha]
  {a b : alpha}
  {S : Finset alpha} :
-- imply
  b ∈ gaugeToggle a S ↔ (b = a ∧ b ∉ S) ∨ (b ≠ a ∧ b ∈ S) := by
-- proof
  apply StatMech.FrontierA.mem_gaugeToggle a b S

/--
[walkOddSupport_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCycleComplete.lean)
-/
@[path]
private lemma walkOddSupport_nil_eq
  [Fintype V]
  [DecidableEq V]
  {x : V} :
-- imply
  walkOddSupport G (.nil : G.Walk x x) = ∅ := by
-- proof
  apply StatMech.FrontierA.walkOddSupport_nil x

/--
[walkOddSupport_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCycleComplete.lean)
-/
@[path]
private lemma walkOddSupport_cons_eq
  [Fintype V]
  [DecidableEq V]
  {u v w : V}
  {p : G.Walk v w}
-- given
  (h : G.Adj u v) :
-- imply
  walkOddSupport G (.cons h p) = gaugeToggle s(u, v) (walkOddSupport G p) := by
-- proof
  apply StatMech.FrontierA.walkOddSupport_cons h p

/--
[walkOddSupport_subset_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCycleComplete.lean)
-/
@[path]
private lemma walkOddSupport_subset_edgeFinset_eq
  [Fintype V]
  [DecidableEq V]
  {x y : V}
  {p : G.Walk x y} :
-- imply
  walkOddSupport G p ⊆ G.edgeFinset := by
-- proof
  apply StatMech.FrontierA.walkOddSupport_subset_edgeFinset p

/--
[even_filter_walkOddSupport_iff_walkParity_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCycleComplete.lean)
-/
@[path]
private lemma even_filter_walkOddSupport_iff_walkParity_false_eq
  [Fintype V]
  [DecidableEq V]
  {A : Finset (Sym2 V)}
  {x y : V}
  {p : G.Walk x y} :
-- imply
  Even (A.filter (fun e => e ∈ walkOddSupport G p)).card ↔ walkParity G A p = false := by
-- proof
  apply StatMech.FrontierA.even_filter_walkOddSupport_iff_walkParity_false A p

/--
[exists_odd_closed_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCycleComplete.lean)
-/
@[path]
private lemma exists_odd_closed_walk_eq
  [Fintype V]
  [DecidableEq V]
  [Nonempty V]
  {q : CycleCompleteConstraint G}
-- given
  (hG : G.Preconnected) :
-- imply
  ∃ (x : V) (p : G.Walk x x), walkParity G q.1 p = true := by
-- proof
  apply StatMech.FrontierA.exists_odd_closed_walk hG q

/--
[cycleCompleteWitnessWalk_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCycleComplete.lean)
-/
@[path]
private lemma cycleCompleteWitnessWalk_odd_eq
  [Fintype V]
  [DecidableEq V]
  [Nonempty V]
  {q : CycleCompleteConstraint G}
-- given
  (hG : G.Preconnected) :
-- imply
  walkParity G q.1 (cycleCompleteWitnessWalk G hG q) = true := by
-- proof
  apply StatMech.FrontierA.cycleCompleteWitnessWalk_odd hG q

/--
[cycleComplete_incidenceCount_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCycleComplete.lean)
-/
@[path]
private lemma cycleComplete_incidenceCount_eq_eq
  [Fintype V]
  [DecidableEq V]
  [Nonempty V]
  {A : Finset G.edgeFinset}
  {q : CycleCompleteConstraint G}
-- given
  (hG : G.Preconnected) :
-- imply
  plaquetteIncidenceCount (cycleCompleteIncidence G hG) A q = (A.filter (fun e => e.1 ∈ walkOddSupport G (cycleCompleteWitnessWalk G hG q))).card := by
-- proof
  apply StatMech.FrontierA.cycleComplete_incidenceCount_eq hG A q

/--
[cycleCompleteEdgeSet_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCycleComplete.lean)
-/
@[path]
private lemma cycleCompleteEdgeSet_subset_eq
  [Fintype V]
  [DecidableEq V]
  {A : Finset G.edgeFinset} :
-- imply
  cycleCompleteEdgeSet G A ⊆ G.edgeFinset := by
-- proof
  apply StatMech.FrontierA.cycleCompleteEdgeSet_subset A

/--
[cycleComplete_incidence_even_iff_walkParity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCycleComplete.lean)
-/
@[path]
private lemma cycleComplete_incidence_even_iff_walkParity_eq
  [Fintype V]
  [DecidableEq V]
  [Nonempty V]
  {A : Finset G.edgeFinset}
  {q : CycleCompleteConstraint G}
-- given
  (hG : G.Preconnected) :
-- imply
  Even (plaquetteIncidenceCount (cycleCompleteIncidence G hG) A q) ↔ walkParity G (cycleCompleteEdgeSet G A) (cycleCompleteWitnessWalk G hG q) = false := by
-- proof
  apply StatMech.FrontierA.cycleComplete_incidence_even_iff_walkParity hG A q

/--
[cycleComplete_isClosed_iff_mem_cutSpace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCycleComplete.lean)
-/
@[path]
private lemma cycleComplete_isClosed_iff_mem_cutSpace_eq
  [Fintype V]
  [DecidableEq V]
  [Nonempty V]
  {A : Finset G.edgeFinset}
-- given
  (hG : G.Preconnected) :
-- imply
  IsClosedPlaquetteSet (cycleCompleteIncidence G hG) A ↔ cycleCompleteEdgeSet G A ∈ cutSpace G := by
-- proof
  apply StatMech.FrontierA.cycleComplete_isClosed_iff_mem_cutSpace hG A

/--
[mem_cycleCompleteEdgePreimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCycleComplete.lean)
-/
@[path]
private lemma mem_cycleCompleteEdgePreimage_eq
  [Fintype V]
  [DecidableEq V]
  {delta : Finset (Sym2 V)}
  {p : G.edgeFinset} :
-- imply
  p ∈ cycleCompleteEdgePreimage G delta ↔ p.1 ∈ delta := by
-- proof
  apply StatMech.FrontierA.mem_cycleCompleteEdgePreimage delta p

/--
[cycleCompleteEdgeSet_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCycleComplete.lean)
-/
@[path]
private lemma cycleCompleteEdgeSet_preimage_eq
  [Fintype V]
  [DecidableEq V]
  {delta : Finset (Sym2 V)}
-- given
  (hdelta : delta ⊆ G.edgeFinset) :
-- imply
  cycleCompleteEdgeSet G (cycleCompleteEdgePreimage G delta) = delta := by
-- proof
  apply StatMech.FrontierA.cycleCompleteEdgeSet_preimage hdelta

/--
[cycleCompleteEdgePreimage_set](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCycleComplete.lean)
-/
@[path]
private lemma cycleCompleteEdgePreimage_set_eq
  [Fintype V]
  [DecidableEq V]
  {A : Finset G.edgeFinset} :
-- imply
  cycleCompleteEdgePreimage G (cycleCompleteEdgeSet G A) = A := by
-- proof
  apply StatMech.FrontierA.cycleCompleteEdgePreimage_set A

/--
[cutSpace_member_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCycleComplete.lean)
-/
@[path]
private lemma cutSpace_member_subset_eq
  [Fintype V]
  [DecidableEq V]
  {delta : Finset (Sym2 V)}
-- given
  (hdelta : delta ∈ cutSpace G) :
-- imply
  delta ⊆ G.edgeFinset := by
-- proof
  apply StatMech.FrontierA.cutSpace_member_subset hdelta

/--
[mem_cycleCompleteClosedFamily_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCycleComplete.lean)
-/
@[path]
private lemma mem_cycleCompleteClosedFamily_iff_eq
  [Fintype V]
  [DecidableEq V]
  [Nonempty V]
  {A : Finset G.edgeFinset}
-- given
  (hG : G.Preconnected) :
-- imply
  A ∈ gaugeClosedSurfaceFamily (cycleCompleteIncidence G hG) ↔ IsClosedPlaquetteSet (cycleCompleteIncidence G hG) A := by
-- proof
  apply StatMech.FrontierA.mem_cycleCompleteClosedFamily_iff hG A

/--
[cycleCompleteSurfaceEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCycleComplete.lean)
-/
@[path]
private lemma cycleCompleteSurfaceEquiv_apply_eq
  [Fintype V]
  [DecidableEq V]
  [Nonempty V]
-- given
  (hG : G.Preconnected)
  (A : {A : Finset G.edgeFinset // A ∈ gaugeClosedSurfaceFamily (cycleCompleteIncidence G hG)}) :
-- imply
  (cycleCompleteSurfaceEquiv G hG A).1 = cycleCompleteEdgeSet G A.1 := by
-- proof
  apply StatMech.FrontierA.cycleCompleteSurfaceEquiv_apply hG A

/--
[cycleCompleteEdgeSet_eq_dualPlaquetteMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCycleComplete.lean)
-/
@[path]
private lemma cycleCompleteEdgeSet_eq_dualPlaquetteMap_eq
  [Fintype V]
  [DecidableEq V]
  {A : Finset G.edgeFinset} :
-- imply
  cycleCompleteEdgeSet G A = A.map (dualPlaquetteEmbedding (Equiv.refl G.edgeFinset)) := by
-- proof
  apply StatMech.FrontierA.cycleCompleteEdgeSet_eq_dualPlaquetteMap A

/--
[cycleComplete_gaugePartition_isingDuality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCycleComplete.lean)
-/
@[path]
private lemma cycleComplete_gaugePartition_isingDuality_eq
  [Fintype V]
  [DecidableEq V]
  [Nonempty V]
  {K : G.edgeFinset → ℝ}
-- given
  (hG : G.Preconnected)
  (hK : ∀ p, 0 < K p) :
-- imply
  (Real.exp (∑ e ∈ G.edgeFinset, dualIsingCoupling (Equiv.refl G.edgeFinset) K e) * 2) * gaugePartition (cycleCompleteIncidence G hG) K = ((2 : ℝ) ^ Fintype.card (CycleCompleteConstraint G) * ∏ p : G.edgeFinset, Real.cosh (K p)) * ZJ G.edgeFinset (dualIsingCoupling (Equiv.refl G.edgeFinset) K) (fun _ => 0) := by
-- proof
  apply StatMech.FrontierA.cycleComplete_gaugePartition_isingDuality hG K hK

/--
[cycleComplete_gaugeWilsonExpectation_eq_dualDisorderRatio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCycleComplete.lean)
-/
@[path]
private lemma cycleComplete_gaugeWilsonExpectation_eq_dualDisorderRatio_eq
  [Fintype V]
  [DecidableEq V]
  [Nonempty V]
  {K : G.edgeFinset → ℝ}
  {L : Finset (CycleCompleteConstraint G)}
  {D : Finset G.edgeFinset}
-- given
  (hG : G.Preconnected)
  (hK : ∀ p, 0 < K p)
  (hD : HasWilsonBoundary (cycleCompleteIncidence G hG) D L) :
-- imply
  gaugeWilsonExpectation (cycleCompleteIncidence G hG) K L = (∑ gamma ∈ shiftedDualCutFamily (G := G) (D.map (dualPlaquetteEmbedding (Equiv.refl G.edgeFinset))), ∏ e ∈ gamma, Real.exp (-2 * dualIsingCoupling (Equiv.refl G.edgeFinset) K e)) / (∑ delta ∈ cutSpace G, ∏ e ∈ delta, Real.exp (-2 * dualIsingCoupling (Equiv.refl G.edgeFinset) K e)) := by
-- proof
  apply StatMech.FrontierA.cycleComplete_gaugeWilsonExpectation_eq_dualDisorderRatio hG K hK L D hD


-- created on 2026-10-23
