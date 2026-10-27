import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalDualEquiv.Part7
open Finset StatMech StatMech.FrontierA


/--
[cubicalLowerXYTrace_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualEquiv.lean)
-/
@[path]
private lemma cubicalLowerXYTrace_injective_eq
  {a b c : Nat}
-- given
  (hb : 0 < b)
  (hc : 0 < c) :
-- imply
  Function.Injective (fun A : ClosedCubicalSurface a b c => cubicalLowerXYTrace A.1) := by
-- proof
  apply StatMech.FrontierA.cubicalLowerXYTrace_injective hb hc

/--
[cubicalVolumeSurface_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualEquiv.lean)
-/
@[path]
private lemma cubicalVolumeSurface_injective_eq
  {a b c : Nat}
-- given
  (hc : 0 < c) :
-- imply
  Function.Injective (cubicalVolumeSurface (a := a) (b := b) (c := c)) := by
-- proof
  apply StatMech.FrontierA.cubicalVolumeSurface_injective hc

/--
[card_closedCubicalSurface_eq_card_cellFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualEquiv.lean)
-/
@[path]
private lemma card_closedCubicalSurface_eq_card_cellFinset_eq
  {a b c : Nat}
-- given
  (hb : 0 < b)
  (hc : 0 < c) :
-- imply
  Fintype.card (ClosedCubicalSurface a b c) = Fintype.card (Finset (CubicalCell a b c)) := by
-- proof
  apply StatMech.FrontierA.card_closedCubicalSurface_eq_card_cellFinset hb hc

/--
[cubicalVolumeSurfaceEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualEquiv.lean)
-/
@[path]
private lemma cubicalVolumeSurfaceEquiv_apply_eq
  {a b c : Nat}
  {S : Finset (CubicalCell a b c)}
-- given
  (hb : 0 < b)
  (hc : 0 < c) :
-- imply
  (cubicalVolumeSurfaceEquiv hb hc S).1 = cubicalVolumeBoundary S := by
-- proof
  apply StatMech.FrontierA.cubicalVolumeSurfaceEquiv_apply hb hc S

/--
[finBackward_eq_some_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualEquiv.lean)
-/
@[path]
private lemma finBackward_eq_some_iff_eq
  {n : Nat}
  {f : Fin (n + 1)}
  {k : Fin n} :
-- imply
  finBackward f = some k ↔ f = k.succ := by
-- proof
  apply StatMech.FrontierA.finBackward_eq_some_iff f k

/--
[finForward_eq_some_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualEquiv.lean)
-/
@[path]
private lemma finForward_eq_some_iff_eq
  {n : Nat}
  {f : Fin (n + 1)}
  {k : Fin n} :
-- imply
  finForward f = some k ↔ f = k.castSucc := by
-- proof
  apply StatMech.FrontierA.finForward_eq_some_iff f k

/--
[mem_cubicalPlaquetteCells_iff_mem_cellFaces](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualEquiv.lean)
-/
@[path]
private lemma mem_cubicalPlaquetteCells_iff_mem_cellFaces_eq
  {a b c : Nat}
  {q : CubicalCell a b c}
  {p : CubicalPlaquette a b c} :
-- imply
  q ∈ cubicalPlaquetteCells p ↔ p ∈ cubicalCellFaces q := by
-- proof
  apply StatMech.FrontierA.mem_cubicalPlaquetteCells_iff_mem_cellFaces q p

/--
[plaquetteIncidenceCount_cellFaces_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualEquiv.lean)
-/
@[path]
private lemma plaquetteIncidenceCount_cellFaces_eq_eq
  {a b c : Nat}
  {S : Finset (CubicalCell a b c)}
  {p : CubicalPlaquette a b c} :
-- imply
  plaquetteIncidenceCount cubicalCellFaces S p = (S.filter fun q => q ∈ cubicalPlaquetteCells p).card := by
-- proof
  apply StatMech.FrontierA.plaquetteIncidenceCount_cellFaces_eq S p

/--
[selectedOptionSpin_ne_iff_not_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualEquiv.lean)
-/
@[path]
private lemma selectedOptionSpin_ne_iff_not_even_eq
  [DecidableEq α]
  {S : Finset α}
  {u v : Option α}
-- given
  (huv : u ≠ v) :
-- imply
  selectedOptionSpin S u ≠ selectedOptionSpin S v ↔ ¬ Even ((S.filter fun q => q ∈ u.toFinset ∪ v.toFinset).card) := by
-- proof
  apply StatMech.FrontierA.selectedOptionSpin_ne_iff_not_even S huv

/--
[finBackward_eq_none_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualEquiv.lean)
-/
@[path]
private lemma finBackward_eq_none_iff_eq
  {n : Nat}
  {f : Fin (n + 1)} :
-- imply
  finBackward f = none ↔ f = 0 := by
-- proof
  apply StatMech.FrontierA.finBackward_eq_none_iff f

/--
[finBackward_ne_finForward](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualEquiv.lean)
-/
@[path]
private lemma finBackward_ne_finForward_eq
  {n : Nat}
  {f : Fin (n + 1)}
-- given
  (hn : 0 < n) :
-- imply
  finBackward f ≠ finForward f := by
-- proof
  apply StatMech.FrontierA.finBackward_ne_finForward hn f

/--
[cubicalDualEnds_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualEquiv.lean)
-/
@[path]
private lemma cubicalDualEnds_ne_eq
  {a b c : Nat}
  {p : CubicalPlaquette a b c}
-- given
  (ha : 0 < a)
  (hb : 0 < b)
  (hc : 0 < c) :
-- imply
  (cubicalDualEnds p).1 ≠ (cubicalDualEnds p).2 := by
-- proof
  apply StatMech.FrontierA.cubicalDualEnds_ne ha hb hc p

/--
[cellFinsetAnchoredEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualEquiv.lean)
-/
@[path]
private lemma cellFinsetAnchoredEquiv_apply_eq
  {a b c : Nat}
  {S : Finset (CubicalCell a b c)}
  {q : Option (CubicalCell a b c)} :
-- imply
  (cellFinsetAnchoredEquiv S).1 q = selectedOptionSpin S q := by
-- proof
  apply StatMech.FrontierA.cellFinsetAnchoredEquiv_apply S q

/--
[multibondCut_cellFinsetAnchored_eq_volumeBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualEquiv.lean)
-/
@[path]
private lemma multibondCut_cellFinsetAnchored_eq_volumeBoundary_eq
  {a b c : Nat}
  {S : Finset (CubicalCell a b c)}
-- given
  (ha : 0 < a)
  (hb : 0 < b)
  (hc : 0 < c) :
-- imply
  multibondCut cubicalDualEnds (cellFinsetAnchoredEquiv S).1 = cubicalVolumeBoundary S := by
-- proof
  apply StatMech.FrontierA.multibondCut_cellFinsetAnchored_eq_volumeBoundary ha hb hc S

/--
[multibondCut_cubicalClosedSurfaceAnchoredEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualEquiv.lean)
-/
@[path]
private lemma multibondCut_cubicalClosedSurfaceAnchoredEquiv_eq
  {a b c : Nat}
  {A : ClosedCubicalSurface a b c}
-- given
  (ha : 0 < a)
  (hb : 0 < b)
  (hc : 0 < c) :
-- imply
  multibondCut cubicalDualEnds (cubicalClosedSurfaceAnchoredEquiv hb hc A).1 = A.1 := by
-- proof
  apply StatMech.FrontierA.multibondCut_cubicalClosedSurfaceAnchoredEquiv ha hb hc A

/--
[cubical_gaugePartition_isingDuality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualEquiv.lean)
-/
@[path]
private lemma cubical_gaugePartition_isingDuality_eq
  {a b c : Nat}
  {K : CubicalPlaquette a b c → Real}
-- given
  (ha : 0 < a)
  (hb : 0 < b)
  (hc : 0 < c)
  (hK : ∀ p, 0 < K p) :
-- imply
  (Real.exp (∑ p : CubicalPlaquette a b c, gaugeDualCoupling (K p)) * 2) * gaugePartition cubicalPlaquetteIncidence K = ((2 : Real) ^ Fintype.card (CubicalEdge a b c) * ∏ p : CubicalPlaquette a b c, Real.cosh (K p)) * multibondIsingPartition cubicalDualEnds (fun p => gaugeDualCoupling (K p)) := by
-- proof
  apply StatMech.FrontierA.cubical_gaugePartition_isingDuality ha hb hc K hK

/--
[cubicalXYWilsonExpectation_eq_typedDisorderRatio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualEquiv.lean)
-/
@[path]
private lemma cubicalXYWilsonExpectation_eq_typedDisorderRatio_eq
  {a b c : Nat}
  {k : Fin (c + 1)}
  {K : CubicalPlaquette a b c → Real}
-- given
  (ha : 0 < a)
  (hb : 0 < b)
  (hc : 0 < c)
  (hK : ∀ p, 0 < K p) :
-- imply
  gaugeWilsonExpectation cubicalPlaquetteIncidence K (cubicalXYLoop k) = (∑ s : AnchoredConfig (CubicalDualVertex a b c) none, ∏ p ∈ multibondCut cubicalDualEnds s.1 ∆ cubicalXYSheet k, Real.exp (-2 * gaugeDualCoupling (K p))) / (∑ s : AnchoredConfig (CubicalDualVertex a b c) none, ∏ p ∈ multibondCut cubicalDualEnds s.1, Real.exp (-2 * gaugeDualCoupling (K p))) := by
-- proof
  apply StatMech.FrontierA.cubicalXYWilsonExpectation_eq_typedDisorderRatio ha hb hc k K hK


-- created on 2026-10-23
