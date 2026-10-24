import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalWilson
open Finset StatMech StatMech.FrontierA


/--
[cubical_hasEvenPlaquetteStarIncidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalWilson.lean)
-/
@[path]
private lemma cubical_hasEvenPlaquetteStarIncidence_eq
  {a b c : Nat} :
-- imply
  HasEvenPlaquetteStarIncidence (cubicalPlaquetteIncidence (a := a) (b := b) (c := c)) cubicalVertexStar := by
-- proof
  apply StatMech.FrontierA.cubical_hasEvenPlaquetteStarIncidence

/--
[cubicalGaugeAction_localGaugeTransform_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalWilson.lean)
-/
@[path]
private lemma cubicalGaugeAction_localGaugeTransform_eq_eq
  {a b c : Nat}
  {K : CubicalPlaquette a b c → Real}
  {v : CubicalVertex a b c}
  {omega : GaugeConfig (CubicalEdge a b c)} :
-- imply
  gaugeAction cubicalPlaquetteIncidence K (localGaugeTransform cubicalVertexStar v omega) = gaugeAction cubicalPlaquetteIncidence K omega := by
-- proof
  apply StatMech.FrontierA.cubicalGaugeAction_localGaugeTransform_eq K v omega

/--
[mem_gaugeSurfaceBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalWilson.lean)
-/
@[path]
private lemma mem_gaugeSurfaceBoundary_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq P]
  {incidence : P → Finset E}
  {A : Finset P}
  {e : E} :
-- imply
  e ∈ gaugeSurfaceBoundary incidence A ↔ ¬ Even (plaquetteIncidenceCount incidence A e) := by
-- proof
  apply StatMech.FrontierA.mem_gaugeSurfaceBoundary incidence A e

/--
[isClosedPlaquetteSet_iff_gaugeSurfaceBoundary_eq_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalWilson.lean)
-/
@[path]
private lemma isClosedPlaquetteSet_iff_gaugeSurfaceBoundary_eq_empty_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq P]
  {incidence : P → Finset E}
  {A : Finset P} :
-- imply
  IsClosedPlaquetteSet incidence A ↔ gaugeSurfaceBoundary incidence A = ∅ := by
-- proof
  apply StatMech.FrontierA.isClosedPlaquetteSet_iff_gaugeSurfaceBoundary_eq_empty incidence A

/--
[hasWilsonBoundary_gaugeSurfaceBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalWilson.lean)
-/
@[path]
private lemma hasWilsonBoundary_gaugeSurfaceBoundary_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq P]
  {incidence : P → Finset E}
  {A : Finset P} :
-- imply
  HasWilsonBoundary incidence A (gaugeSurfaceBoundary incidence A) := by
-- proof
  apply StatMech.FrontierA.hasWilsonBoundary_gaugeSurfaceBoundary incidence A

/--
[gaugeSurfaceBoundary_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalWilson.lean)
-/
@[path]
private lemma gaugeSurfaceBoundary_singleton_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype P]
  [DecidableEq P]
  {incidence : P → Finset E}
  {p : P} :
-- imply
  gaugeSurfaceBoundary incidence {p} = incidence p := by
-- proof
  apply StatMech.FrontierA.gaugeSurfaceBoundary_singleton incidence p

/--
[cubicalXYSheet_hasWilsonBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalWilson.lean)
-/
@[path]
private lemma cubicalXYSheet_hasWilsonBoundary_eq
  {a b c : Nat}
  {k : Fin (c + 1)} :
-- imply
  HasWilsonBoundary (cubicalPlaquetteIncidence (a := a) (b := b) (c := c)) (cubicalXYSheet k) (cubicalXYLoop k) := by
-- proof
  apply StatMech.FrontierA.cubicalXYSheet_hasWilsonBoundary k

/--
[cubicalXYWilsonExpectation_eq_dualDisorderRatio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalWilson.lean)
-/
@[path]
private lemma cubicalXYWilsonExpectation_eq_dualDisorderRatio_eq
  {a b c : Nat}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {k : Fin (c + 1)}
  {K : CubicalPlaquette a b c → Real}
  {dualEdge : CubicalPlaquette a b c ≃ G.edgeFinset}
-- given
  (hK : ∀ p, 0 < K p)
  (closedEquiv : {A : Finset (CubicalPlaquette a b c) // A ∈ gaugeClosedSurfaceFamily cubicalPlaquetteIncidence} ≃ {delta : Finset (Sym2 V) // delta ∈ StatMech.Ising.cutSpace G})
  (hclosed : ∀ A, (closedEquiv A).1 = A.1.map (dualPlaquetteEmbedding dualEdge)) :
-- imply
  gaugeWilsonExpectation cubicalPlaquetteIncidence K (cubicalXYLoop k) = (∑ gamma ∈ shiftedDualCutFamily (G := G) ((cubicalXYSheet k).map (dualPlaquetteEmbedding dualEdge)), ∏ e ∈ gamma, Real.exp (-2 * dualIsingCoupling dualEdge K e)) / (∑ delta ∈ StatMech.Ising.cutSpace G, ∏ e ∈ delta, Real.exp (-2 * dualIsingCoupling dualEdge K e)) := by
-- proof
  apply StatMech.FrontierA.cubicalXYWilsonExpectation_eq_dualDisorderRatio k K hK dualEdge closedEquiv hclosed


-- created on 2026-10-23
