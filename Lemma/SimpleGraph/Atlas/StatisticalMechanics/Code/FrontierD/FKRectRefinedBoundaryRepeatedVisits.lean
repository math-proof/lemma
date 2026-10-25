import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedBoundaryRepeatedVisits
open StatMech StatMech.FrontierD


/--
[fkRectRefinedBondCenter_add_center](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryRepeatedVisits.lean)
-/
@[path]
private lemma fkRectRefinedBondCenter_add_center_eq
  {c t : Int × Int}
  {side : FKMedialSide} :
-- imply
  fkRectRefinedBondCenter (c.1 + t.1, c.2 + t.2) side = ((fkRectRefinedBondCenter c side).1 + t.1, (fkRectRefinedBondCenter c side).2 + t.2) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedBondCenter_add_center c t side

/--
[fkRectRefinedBoundaryDarts_add_center](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryRepeatedVisits.lean)
-/
@[path]
private lemma fkRectRefinedBoundaryDarts_add_center_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialDart T}
  {c t : Int × Int}
  {n : Nat} :
-- imply
  fkRectRefinedBoundaryDarts pairing d (c.1 + t.1, c.2 + t.2) n = (fkRectRefinedBoundaryDarts pairing d c n).map (fkRectIntegralSquareDartTranslate t) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedBoundaryDarts_add_center pairing d c t n

/--
[fkRectRefinedRawInteraction_translated_boundary_eq_matchedVisits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryRepeatedVisits.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_translated_boundary_eq_matchedVisits_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {d : FKMedialDart R.medialTorus}
  {n : Nat}
  {a b u : Int × Int}
-- given
  (heF : e ∉ F)
  (hcolor : fkMedialCheckerColor d = fkMedialCheckerColor (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))
  (hrelative : (a.1 - b.1, a.2 - b.2) = (4 * (fkRectSquareDeckTranslation R u).1, 4 * (fkRectSquareDeckTranslation R u).2)) :
-- imply
  let pairing := fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F) let c := fkRectRefinedBoundaryCanonicalCenter R d let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R) fkRectRefinedRawInteraction (((fkRectRefinedBoundaryDarts pairing d c n).map (fkRectIntegralSquareDartTranslate a)).map (fkRectIntegralSquareDartMod L)) (((fkRectRefinedPrimalEdgeDarts R e).map (fkRectIntegralSquareDartTranslate b)).map (fkRectIntegralSquareDartMod L)) = fkRectRefinedBoundaryMatchedVisitTrace R pairing e d (c.1 + (a.1 - b.1), c.2 + (a.2 - b.2)) n := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_translated_boundary_eq_matchedVisits R F e heF d n a b u hcolor hrelative

/--
[fkRectRefinedRawInteraction_repeated_boundary_edge_eq_sum_matchedVisits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryRepeatedVisits.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_repeated_boundary_edge_eq_sum_matchedVisits_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {w z : Int × Int}
-- given
  (heF : e ∉ F) :
-- imply
  let pairing := fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F) let d := fkMedialWestDart (fkRectMedialVertexOfEdge R e) let c := fkRectRefinedBoundaryCanonicalCenter R d let n := orderOf (fkMedialBoundaryStep pairing) let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R) let U : Int × Int := (4 * (fkRectSquareDeckTranslation R w).1, 4 * (fkRectSquareDeckTranslation R w).2) let V : Int × Int := (4 * (fkRectSquareDeckTranslation R z).1, 4 * (fkRectSquareDeckTranslation R z).2) fkRectRefinedRawInteraction ((fkRectRepeatTranslatedDartPath (fkRectRefinedBoundaryDarts pairing d c n) U L).map (fkRectIntegralSquareDartMod L)) ((fkRectRepeatTranslatedDartPath (fkRectRefinedPrimalEdgeDarts R e) V L).map (fkRectIntegralSquareDartMod L)) = ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, fkRectRefinedBoundaryMatchedVisitTrace R pairing e d (c.1 + ((fkRectNatScale i U).1 - (fkRectNatScale j V).1), c.2 + ((fkRectNatScale i U).2 - (fkRectNatScale j V).2)) n := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_repeated_boundary_edge_eq_sum_matchedVisits R F e heF w z

/--
[fkRectRefinedRawInteraction_translated_boundary_openEdge_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryRepeatedVisits.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_translated_boundary_openEdge_eq_zero_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {d : FKMedialDart R.medialTorus}
  {n : Nat}
  {a b u : Int × Int}
-- given
  (heF : e ∈ F)
  (hrelative : (a.1 - b.1, a.2 - b.2) = (4 * (fkRectSquareDeckTranslation R u).1, 4 * (fkRectSquareDeckTranslation R u).2)) :
-- imply
  let pairing := fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F) let c := fkRectRefinedBoundaryCanonicalCenter R d let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R) fkRectRefinedRawInteraction (((fkRectRefinedBoundaryDarts pairing d c n).map (fkRectIntegralSquareDartTranslate a)).map (fkRectIntegralSquareDartMod L)) (((fkRectRefinedPrimalEdgeDarts R e).map (fkRectIntegralSquareDartTranslate b)).map (fkRectIntegralSquareDartMod L)) = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_translated_boundary_openEdge_eq_zero R F e heF d n a b u hrelative

/--
[fkRectRefinedRawInteraction_repeated_boundary_openEdge_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryRepeatedVisits.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_repeated_boundary_openEdge_eq_zero_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {d : FKMedialDart R.medialTorus}
  {n : Nat}
  {w z : Int × Int}
-- given
  (heF : e ∈ F) :
-- imply
  let pairing := fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F) let c := fkRectRefinedBoundaryCanonicalCenter R d let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R) let U : Int × Int := (4 * (fkRectSquareDeckTranslation R w).1, 4 * (fkRectSquareDeckTranslation R w).2) let V : Int × Int := (4 * (fkRectSquareDeckTranslation R z).1, 4 * (fkRectSquareDeckTranslation R z).2) fkRectRefinedRawInteraction ((fkRectRepeatTranslatedDartPath (fkRectRefinedBoundaryDarts pairing d c n) U L).map (fkRectIntegralSquareDartMod L)) ((fkRectRepeatTranslatedDartPath (fkRectRefinedPrimalEdgeDarts R e) V L).map (fkRectIntegralSquareDartMod L)) = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_repeated_boundary_openEdge_eq_zero R F e heF d n w z

/--
[fkRectRefinedBoundaryMatchedVisitTrace_nonneg_of_avoid_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryRepeatedVisits.lean)
-/
@[path]
private lemma fkRectRefinedBoundaryMatchedVisitTrace_nonneg_of_avoid_east_eq
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {e : R.EdgeIndex}
  {d : FKMedialDart R.medialTorus}
  {c : Int × Int}
  {n : Nat}
-- given
  (hcolor : fkMedialCheckerColor d = fkMedialCheckerColor (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))
  (havoid : ∀ k : Nat, (fkMedialBoundaryStep pairing)^[k] d ≠ fkMedialEastDart (fkRectMedialVertexOfEdge R e)) :
-- imply
  0 ≤ fkRectRefinedBoundaryMatchedVisitTrace R pairing e d c n := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedBoundaryMatchedVisitTrace_nonneg_of_avoid_east R pairing e d c n hcolor havoid

/--
[fkRectRefinedBoundaryMatchedVisitTrace_eq_zero_of_avoid_west_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryRepeatedVisits.lean)
-/
@[path]
private lemma fkRectRefinedBoundaryMatchedVisitTrace_eq_zero_of_avoid_west_east_eq
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {e : R.EdgeIndex}
  {d : FKMedialDart R.medialTorus}
  {c : Int × Int}
  {n : Nat}
-- given
  (hcolor : fkMedialCheckerColor d = fkMedialCheckerColor (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))
  (hwest : ∀ k : Nat, (fkMedialBoundaryStep pairing)^[k] d ≠ fkMedialWestDart (fkRectMedialVertexOfEdge R e))
  (heast : ∀ k : Nat, (fkMedialBoundaryStep pairing)^[k] d ≠ fkMedialEastDart (fkRectMedialVertexOfEdge R e)) :
-- imply
  fkRectRefinedBoundaryMatchedVisitTrace R pairing e d c n = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedBoundaryMatchedVisitTrace_eq_zero_of_avoid_west_east R pairing e d c n hcolor hwest heast

/--
[fkRectRefinedBoundaryMatchedVisitTrace_canonical_pos_of_avoid_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryRepeatedVisits.lean)
-/
@[path]
private lemma fkRectRefinedBoundaryMatchedVisitTrace_canonical_pos_of_avoid_east_eq
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {e : R.EdgeIndex}
  {n : Nat}
-- given
  (hn : 0 < n)
  (havoid : ∀ k : Nat, (fkMedialBoundaryStep pairing)^[k] (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) ≠ fkMedialEastDart (fkRectMedialVertexOfEdge R e)) :
-- imply
  0 < fkRectRefinedBoundaryMatchedVisitTrace R pairing e (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkRectRefinedBoundaryCanonicalCenter R (fkMedialWestDart (fkRectMedialVertexOfEdge R e))) n := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedBoundaryMatchedVisitTrace_canonical_pos_of_avoid_east R pairing e n hn havoid

/--
[fkRectRefinedRawInteraction_repeated_boundary_edge_ne_zero_of_avoid_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryRepeatedVisits.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_repeated_boundary_edge_ne_zero_of_avoid_east_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {w z : Int × Int}
-- given
  (heF : e ∉ F)
  (havoid : ∀ k : Nat, let pairing := fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F) (fkMedialBoundaryStep pairing)^[k] (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) ≠ fkMedialEastDart (fkRectMedialVertexOfEdge R e)) :
-- imply
  let pairing := fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F) let d := fkMedialWestDart (fkRectMedialVertexOfEdge R e) let c := fkRectRefinedBoundaryCanonicalCenter R d let n := orderOf (fkMedialBoundaryStep pairing) let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R) let U : Int × Int := (4 * (fkRectSquareDeckTranslation R w).1, 4 * (fkRectSquareDeckTranslation R w).2) let V : Int × Int := (4 * (fkRectSquareDeckTranslation R z).1, 4 * (fkRectSquareDeckTranslation R z).2) fkRectRefinedRawInteraction ((fkRectRepeatTranslatedDartPath (fkRectRefinedBoundaryDarts pairing d c n) U L).map (fkRectIntegralSquareDartMod L)) ((fkRectRepeatTranslatedDartPath (fkRectRefinedPrimalEdgeDarts R e) V L).map (fkRectIntegralSquareDartMod L)) ≠ 0 := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_repeated_boundary_edge_ne_zero_of_avoid_east R F e heF w z havoid

/--
[fkRectRefinedRawInteraction_repeated_boundary_edge_ne_zero_of_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryRepeatedVisits.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_repeated_boundary_edge_ne_zero_of_not_reachable_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {w z : Int × Int}
-- given
  (heF : e ∉ F)
  (hsep : ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e))) :
-- imply
  let pairing := fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F) let d := fkMedialWestDart (fkRectMedialVertexOfEdge R e) let c := fkRectRefinedBoundaryCanonicalCenter R d let n := orderOf (fkMedialBoundaryStep pairing) let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R) let U : Int × Int := (4 * (fkRectSquareDeckTranslation R w).1, 4 * (fkRectSquareDeckTranslation R w).2) let V : Int × Int := (4 * (fkRectSquareDeckTranslation R z).1, 4 * (fkRectSquareDeckTranslation R z).2) fkRectRefinedRawInteraction ((fkRectRepeatTranslatedDartPath (fkRectRefinedBoundaryDarts pairing d c n) U L).map (fkRectIntegralSquareDartMod L)) ((fkRectRepeatTranslatedDartPath (fkRectRefinedPrimalEdgeDarts R e) V L).map (fkRectIntegralSquareDartMod L)) ≠ 0 := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_repeated_boundary_edge_ne_zero_of_not_reachable R F e heF w z hsep


-- created on 2026-10-23
