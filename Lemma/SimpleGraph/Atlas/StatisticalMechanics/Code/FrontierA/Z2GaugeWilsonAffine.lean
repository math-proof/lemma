import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonAffine
open Finset StatMech StatMech.FrontierA


/--
[plaquetteIncidenceCount_eq_filter_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonAffine.lean)
-/
@[path]
private lemma plaquetteIncidenceCount_eq_filter_card_eq
  [Fintype E]
  [DecidableEq E]
  {incidence : P → Finset E}
  {A : Finset P}
  {e : E} :
-- imply
  plaquetteIncidenceCount incidence A e = (A.filter fun p => e ∈ incidence p).card := by
-- proof
  apply StatMech.FrontierA.plaquetteIncidenceCount_eq_filter_card incidence A e

/--
[filter_symmDiff_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonAffine.lean)
-/
@[path]
private lemma filter_symmDiff_eq_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Finset P}
  [DecidablePred q]
-- given
  (q : P → Prop) :
-- imply
  (A ∆ B).filter q = A.filter q ∆ B.filter q := by
-- proof
  apply StatMech.FrontierA.filter_symmDiff_eq A B q

/--
[card_symmDiff_add_twice_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonAffine.lean)
-/
@[path]
private lemma card_symmDiff_add_twice_inter_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Finset P} :
-- imply
  (A ∆ B).card + 2 * (A ∩ B).card = A.card + B.card := by
-- proof
  apply StatMech.FrontierA.card_symmDiff_add_twice_inter A B

/--
[even_plaquetteIncidenceCount_symmDiff_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonAffine.lean)
-/
@[path]
private lemma even_plaquetteIncidenceCount_symmDiff_iff_eq
  [Fintype E]
  [DecidableEq E]
  {incidence : P → Finset E}
  {A B : Finset P}
  {e : E} :
-- imply
  Even (plaquetteIncidenceCount incidence (A ∆ B) e) ↔ (Even (plaquetteIncidenceCount incidence A e) ↔ Even (plaquetteIncidenceCount incidence B e)) := by
-- proof
  apply StatMech.FrontierA.even_plaquetteIncidenceCount_symmDiff_iff incidence A B e

/--
[mem_gaugeClosedSurfaceFamily_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonAffine.lean)
-/
@[path]
private lemma mem_gaugeClosedSurfaceFamily_iff_eq
  [Fintype E]
  [DecidableEq E]
  {incidence : P → Finset E}
  {A : Finset P} :
-- imply
  A ∈ gaugeClosedSurfaceFamily incidence ↔ IsClosedPlaquetteSet incidence A := by
-- proof
  apply StatMech.FrontierA.mem_gaugeClosedSurfaceFamily_iff incidence A

/--
[mem_gaugeWilsonSurfaceFamily_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonAffine.lean)
-/
@[path]
private lemma mem_gaugeWilsonSurfaceFamily_iff_eq
  [Fintype E]
  [DecidableEq E]
  {incidence : P → Finset E}
  {L : Finset E}
  {A : Finset P} :
-- imply
  A ∈ gaugeWilsonSurfaceFamily incidence L ↔ HasWilsonBoundary incidence A L := by
-- proof
  apply StatMech.FrontierA.mem_gaugeWilsonSurfaceFamily_iff incidence L A

/--
[hasWilsonBoundary_iff_symmDiff_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonAffine.lean)
-/
@[path]
private lemma hasWilsonBoundary_iff_symmDiff_closed_eq
  [Fintype E]
  [DecidableEq E]
  {incidence : P → Finset E}
  {L : Finset E}
  {D A : Finset P}
-- given
  (hD : HasWilsonBoundary incidence D L) :
-- imply
  HasWilsonBoundary incidence A L ↔ IsClosedPlaquetteSet incidence (A ∆ D) := by
-- proof
  apply StatMech.FrontierA.hasWilsonBoundary_iff_symmDiff_closed incidence L D A hD

/--
[map_symmDiff_embedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonAffine.lean)
-/
@[path]
private lemma map_symmDiff_embedding_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq alpha]
  [DecidableEq beta]
  {f : alpha ↪ beta}
  {A B : Finset alpha} :
-- imply
  (A ∆ B).map f = A.map f ∆ B.map f := by
-- proof
  apply StatMech.FrontierA.map_symmDiff_embedding f A B

/--
[gaugeWilsonShiftedCutEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonAffine.lean)
-/
@[path]
private lemma gaugeWilsonShiftedCutEquiv_apply_eq
  [Fintype E]
  [DecidableEq E]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {incidence : P → Finset E}
  {L : Finset E}
  {dualEdge : P ≃ G.edgeFinset}
  {D : Finset P}
-- given
  (closedEquiv : {A : Finset P // A ∈ gaugeClosedSurfaceFamily incidence} ≃ {delta : Finset (Sym2 V) // delta ∈ StatMech.Ising.cutSpace G})
  (hclosed : ∀ A, (closedEquiv A).1 = A.1.map (dualPlaquetteEmbedding dualEdge))
  (hD : HasWilsonBoundary incidence D L)
  (A : {A : Finset P // A ∈ gaugeWilsonSurfaceFamily incidence L}) :
-- imply
  (gaugeWilsonShiftedCutEquiv incidence L dualEdge closedEquiv D hD A).1 = A.1.map (dualPlaquetteEmbedding dualEdge) := by
-- proof
  apply StatMech.FrontierA.gaugeWilsonShiftedCutEquiv_apply incidence L dualEdge closedEquiv hclosed D hD A

/--
[gaugeWilsonExpectation_eq_dualDisorderRatio_of_sheet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonAffine.lean)
-/
@[path]
private lemma gaugeWilsonExpectation_eq_dualDisorderRatio_of_sheet_eq
  [Fintype E]
  [DecidableEq E]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {incidence : P → Finset E}
  {K : P → ℝ}
  {L : Finset E}
  {dualEdge : P ≃ G.edgeFinset}
  {D : Finset P}
-- given
  (hK : ∀ p, 0 < K p)
  (closedEquiv : {A : Finset P // A ∈ gaugeClosedSurfaceFamily incidence} ≃ {delta : Finset (Sym2 V) // delta ∈ StatMech.Ising.cutSpace G})
  (hclosed : ∀ A, (closedEquiv A).1 = A.1.map (dualPlaquetteEmbedding dualEdge))
  (hD : HasWilsonBoundary incidence D L) :
-- imply
  gaugeWilsonExpectation incidence K L = (∑ gamma ∈ shiftedDualCutFamily (G := G) (D.map (dualPlaquetteEmbedding dualEdge)), ∏ e ∈ gamma, Real.exp (-2 * dualIsingCoupling dualEdge K e)) / (∑ delta ∈ StatMech.Ising.cutSpace G, ∏ e ∈ delta, Real.exp (-2 * dualIsingCoupling dualEdge K e)) := by
-- proof
  apply StatMech.FrontierA.gaugeWilsonExpectation_eq_dualDisorderRatio_of_sheet incidence K hK L dualEdge closedEquiv hclosed D hD


-- created on 2026-10-23
