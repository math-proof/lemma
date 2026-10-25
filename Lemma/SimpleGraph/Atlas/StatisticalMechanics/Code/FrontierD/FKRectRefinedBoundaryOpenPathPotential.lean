import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedBoundaryOpenPathPotential
open StatMech StatMech.FrontierD


/--
[fkRectRefinedRawInteraction_repeated_boundary_openEdgeOnce_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryOpenPathPotential.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_repeated_boundary_openEdgeOnce_eq_zero_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {d : FKMedialDart R.medialTorus}
  {n : Nat}
  {s w : Int × Int}
-- given
  (heF : e ∈ F) :
-- imply
  let pairing := fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F) let c := fkRectRefinedBoundaryCanonicalCenter R d let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R) let S : Int × Int := (4 * (fkRectSquareDeckTranslation R s).1, 4 * (fkRectSquareDeckTranslation R s).2) let U : Int × Int := (4 * (fkRectSquareDeckTranslation R w).1, 4 * (fkRectSquareDeckTranslation R w).2) fkRectRefinedRawInteraction ((fkRectRepeatTranslatedDartPath (fkRectRefinedBoundaryDarts pairing d c n) U L).map (fkRectIntegralSquareDartMod L)) (((fkRectRefinedPrimalEdgeDarts R e).map (fkRectIntegralSquareDartTranslate S)).map (fkRectIntegralSquareDartMod L)) = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_repeated_boundary_openEdgeOnce_eq_zero R F e heF d n s w

/--
[fkRectRefinedRawInteraction_repeated_boundary_openEdgeReverseOnce_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryOpenPathPotential.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_repeated_boundary_openEdgeReverseOnce_eq_zero_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {d : FKMedialDart R.medialTorus}
  {n : Nat}
  {s w : Int × Int}
-- given
  (heF : e ∈ F) :
-- imply
  let pairing := fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F) let c := fkRectRefinedBoundaryCanonicalCenter R d let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R) let S : Int × Int := (4 * (fkRectSquareDeckTranslation R s).1, 4 * (fkRectSquareDeckTranslation R s).2) let U : Int × Int := (4 * (fkRectSquareDeckTranslation R w).1, 4 * (fkRectSquareDeckTranslation R w).2) fkRectRefinedRawInteraction ((fkRectRepeatTranslatedDartPath (fkRectRefinedBoundaryDarts pairing d c n) U L).map (fkRectIntegralSquareDartMod L)) (((fkRectIntegralSquareDartListReverse (fkRectRefinedPrimalEdgeDarts R e)).map (fkRectIntegralSquareDartTranslate S)).map (fkRectIntegralSquareDartMod L)) = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_repeated_boundary_openEdgeReverseOnce_eq_zero R F e heF d n s w

/--
[fkRectRefinedRawInteraction_repeated_boundary_edgeOnce_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryOpenPathPotential.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_repeated_boundary_edgeOnce_ne_zero_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {w : Int × Int}
-- given
  (heF : e ∉ F)
  (hsep : ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e))) :
-- imply
  let pairing := fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F) let d := fkMedialWestDart (fkRectMedialVertexOfEdge R e) let c := fkRectRefinedBoundaryCanonicalCenter R d let n := orderOf (fkMedialBoundaryStep pairing) let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R) let U : Int × Int := (4 * (fkRectSquareDeckTranslation R w).1, 4 * (fkRectSquareDeckTranslation R w).2) fkRectRefinedRawInteraction ((fkRectRepeatTranslatedDartPath (fkRectRefinedBoundaryDarts pairing d c n) U L).map (fkRectIntegralSquareDartMod L)) ((fkRectRefinedPrimalEdgeDarts R e).map (fkRectIntegralSquareDartMod L)) ≠ 0 := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_repeated_boundary_edgeOnce_ne_zero R F e heF w hsep

/--
[fkRectRefinedRawInteraction_repeated_west_boundary_edgeOnce_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryOpenPathPotential.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_repeated_west_boundary_edgeOnce_pos_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {w : Int × Int}
-- given
  (heF : e ∉ F)
  (hsep : ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e))) :
-- imply
  let pairing := fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F) let d := fkMedialWestDart (fkRectMedialVertexOfEdge R e) let c := fkRectRefinedBoundaryCanonicalCenter R d let n := orderOf (fkMedialBoundaryStep pairing) let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R) let U : Int × Int := (4 * (fkRectSquareDeckTranslation R w).1, 4 * (fkRectSquareDeckTranslation R w).2) 0 < fkRectRefinedRawInteraction ((fkRectRepeatTranslatedDartPath (fkRectRefinedBoundaryDarts pairing d c n) U L).map (fkRectIntegralSquareDartMod L)) ((fkRectRefinedPrimalEdgeDarts R e).map (fkRectIntegralSquareDartMod L)) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_repeated_west_boundary_edgeOnce_pos R F e heF w hsep

/--
[fkRectRefinedRawInteraction_repeated_west_boundary_edge_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryOpenPathPotential.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_repeated_west_boundary_edge_pos_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {w z : Int × Int}
-- given
  (heF : e ∉ F)
  (hsep : ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e))) :
-- imply
  let pairing := fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F) let d := fkMedialWestDart (fkRectMedialVertexOfEdge R e) let c := fkRectRefinedBoundaryCanonicalCenter R d let n := orderOf (fkMedialBoundaryStep pairing) let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R) let U : Int × Int := (4 * (fkRectSquareDeckTranslation R w).1, 4 * (fkRectSquareDeckTranslation R w).2) let V : Int × Int := (4 * (fkRectSquareDeckTranslation R z).1, 4 * (fkRectSquareDeckTranslation R z).2) 0 < fkRectRefinedRawInteraction ((fkRectRepeatTranslatedDartPath (fkRectRefinedBoundaryDarts pairing d c n) U L).map (fkRectIntegralSquareDartMod L)) ((fkRectRepeatTranslatedDartPath (fkRectRefinedPrimalEdgeDarts R e) V L).map (fkRectIntegralSquareDartMod L)) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_repeated_west_boundary_edge_pos R F e heF w z hsep

/--
[fkRectRefinedBoundaryMatchedVisitTrace_nonpos_of_avoid_west](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryOpenPathPotential.lean)
-/
@[path]
private lemma fkRectRefinedBoundaryMatchedVisitTrace_nonpos_of_avoid_west_eq
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {e : R.EdgeIndex}
  {d : FKMedialDart R.medialTorus}
  {c : Int × Int}
  {n : Nat}
-- given
  (hcolor : fkMedialCheckerColor d = fkMedialCheckerColor (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
  (havoid : ∀ k : Nat, (fkMedialBoundaryStep pairing)^[k] d ≠ fkMedialWestDart (fkRectMedialVertexOfEdge R e)) :
-- imply
  fkRectRefinedBoundaryMatchedVisitTrace R pairing e d c n ≤ 0 := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedBoundaryMatchedVisitTrace_nonpos_of_avoid_west R pairing e d c n hcolor havoid

/--
[fkRectRefinedBoundaryMatchedVisitTrace_canonical_neg_of_avoid_west](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryOpenPathPotential.lean)
-/
@[path]
private lemma fkRectRefinedBoundaryMatchedVisitTrace_canonical_neg_of_avoid_west_eq
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {e : R.EdgeIndex}
  {n : Nat}
-- given
  (hn : 0 < n)
  (havoid : ∀ k : Nat, (fkMedialBoundaryStep pairing)^[k] (fkMedialEastDart (fkRectMedialVertexOfEdge R e)) ≠ fkMedialWestDart (fkRectMedialVertexOfEdge R e)) :
-- imply
  fkRectRefinedBoundaryMatchedVisitTrace R pairing e (fkMedialEastDart (fkRectMedialVertexOfEdge R e)) (fkRectRefinedBoundaryCanonicalCenter R (fkMedialEastDart (fkRectMedialVertexOfEdge R e))) n < 0 := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedBoundaryMatchedVisitTrace_canonical_neg_of_avoid_west R pairing e n hn havoid

/--
[fkRectRefinedRawInteraction_repeated_east_boundary_edgeOnce_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryOpenPathPotential.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_repeated_east_boundary_edgeOnce_neg_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {w : Int × Int}
-- given
  (heF : e ∉ F)
  (hsep : ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e))) :
-- imply
  let pairing := fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F) let d := fkMedialEastDart (fkRectMedialVertexOfEdge R e) let c := fkRectRefinedBoundaryCanonicalCenter R d let n := orderOf (fkMedialBoundaryStep pairing) let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R) let U : Int × Int := (4 * (fkRectSquareDeckTranslation R w).1, 4 * (fkRectSquareDeckTranslation R w).2) fkRectRefinedRawInteraction ((fkRectRepeatTranslatedDartPath (fkRectRefinedBoundaryDarts pairing d c n) U L).map (fkRectIntegralSquareDartMod L)) ((fkRectRefinedPrimalEdgeDarts R e).map (fkRectIntegralSquareDartMod L)) < 0 := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_repeated_east_boundary_edgeOnce_neg R F e heF w hsep

/--
[fkRectRefinedRawInteraction_repeated_east_boundary_edge_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryOpenPathPotential.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_repeated_east_boundary_edge_neg_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {w z : Int × Int}
-- given
  (heF : e ∉ F)
  (hsep : ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e))) :
-- imply
  let pairing := fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F) let d := fkMedialEastDart (fkRectMedialVertexOfEdge R e) let c := fkRectRefinedBoundaryCanonicalCenter R d let n := orderOf (fkMedialBoundaryStep pairing) let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R) let U : Int × Int := (4 * (fkRectSquareDeckTranslation R w).1, 4 * (fkRectSquareDeckTranslation R w).2) let V : Int × Int := (4 * (fkRectSquareDeckTranslation R z).1, 4 * (fkRectSquareDeckTranslation R z).2) fkRectRefinedRawInteraction ((fkRectRepeatTranslatedDartPath (fkRectRefinedBoundaryDarts pairing d c n) U L).map (fkRectIntegralSquareDartMod L)) ((fkRectRepeatTranslatedDartPath (fkRectRefinedPrimalEdgeDarts R e) V L).map (fkRectIntegralSquareDartMod L)) < 0 := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_repeated_east_boundary_edge_neg R F e heF w z hsep

/--
[fkRectRefinedRawInteraction_repeated_boundary_edgeOnce_nonpos_of_avoid_west](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryOpenPathPotential.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_repeated_boundary_edgeOnce_nonpos_of_avoid_west_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {d : FKMedialDart R.medialTorus}
  {w : Int × Int}
-- given
  (heF : e ∉ F)
  (hcolor : fkMedialCheckerColor d = fkMedialCheckerColor (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))
  (havoid : ∀ k : Nat, let pairing := fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F) (fkMedialBoundaryStep pairing)^[k] d ≠ fkMedialWestDart (fkRectMedialVertexOfEdge R e)) :
-- imply
  let pairing := fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F) let c := fkRectRefinedBoundaryCanonicalCenter R d let n := orderOf (fkMedialBoundaryStep pairing) let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R) let U : Int × Int := (4 * (fkRectSquareDeckTranslation R w).1, 4 * (fkRectSquareDeckTranslation R w).2) fkRectRefinedRawInteraction ((fkRectRepeatTranslatedDartPath (fkRectRefinedBoundaryDarts pairing d c n) U L).map (fkRectIntegralSquareDartMod L)) ((fkRectRefinedPrimalEdgeDarts R e).map (fkRectIntegralSquareDartMod L)) ≤ 0 := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_repeated_boundary_edgeOnce_nonpos_of_avoid_west R F e heF d w hcolor havoid

/--
[fkRectRefinedRawInteraction_repeated_boundary_edgeOnce_eq_zero_of_avoid_west_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryOpenPathPotential.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_repeated_boundary_edgeOnce_eq_zero_of_avoid_west_east_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {d : FKMedialDart R.medialTorus}
  {w : Int × Int}
-- given
  (heF : e ∉ F)
  (hcolor : fkMedialCheckerColor d = fkMedialCheckerColor (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))
  (hwest : ∀ k : Nat, let pairing := fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F) (fkMedialBoundaryStep pairing)^[k] d ≠ fkMedialWestDart (fkRectMedialVertexOfEdge R e))
  (heast : ∀ k : Nat, let pairing := fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F) (fkMedialBoundaryStep pairing)^[k] d ≠ fkMedialEastDart (fkRectMedialVertexOfEdge R e)) :
-- imply
  let pairing := fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F) let c := fkRectRefinedBoundaryCanonicalCenter R d let n := orderOf (fkMedialBoundaryStep pairing) let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R) let U : Int × Int := (4 * (fkRectSquareDeckTranslation R w).1, 4 * (fkRectSquareDeckTranslation R w).2) fkRectRefinedRawInteraction ((fkRectRepeatTranslatedDartPath (fkRectRefinedBoundaryDarts pairing d c n) U L).map (fkRectIntegralSquareDartMod L)) ((fkRectRefinedPrimalEdgeDarts R e).map (fkRectIntegralSquareDartMod L)) = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_repeated_boundary_edgeOnce_eq_zero_of_avoid_west_east R F e heF d w hcolor hwest heast

/--
[fkRectRefinedRawInteraction_repeated_boundary_edge_nonpos_of_avoid_west](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryOpenPathPotential.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_repeated_boundary_edge_nonpos_of_avoid_west_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {d : FKMedialDart R.medialTorus}
  {w z : Int × Int}
-- given
  (heF : e ∉ F)
  (hcolor : fkMedialCheckerColor d = fkMedialCheckerColor (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))
  (havoid : ∀ k : Nat, let pairing := fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F) (fkMedialBoundaryStep pairing)^[k] d ≠ fkMedialWestDart (fkRectMedialVertexOfEdge R e)) :
-- imply
  let pairing := fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F) let c := fkRectRefinedBoundaryCanonicalCenter R d let n := orderOf (fkMedialBoundaryStep pairing) let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R) let U : Int × Int := (4 * (fkRectSquareDeckTranslation R w).1, 4 * (fkRectSquareDeckTranslation R w).2) let V : Int × Int := (4 * (fkRectSquareDeckTranslation R z).1, 4 * (fkRectSquareDeckTranslation R z).2) fkRectRefinedRawInteraction ((fkRectRepeatTranslatedDartPath (fkRectRefinedBoundaryDarts pairing d c n) U L).map (fkRectIntegralSquareDartMod L)) ((fkRectRepeatTranslatedDartPath (fkRectRefinedPrimalEdgeDarts R e) V L).map (fkRectIntegralSquareDartMod L)) ≤ 0 := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_repeated_boundary_edge_nonpos_of_avoid_west R F e heF d w z hcolor havoid

/--
[fkRectRefinedRawInteraction_repeated_boundary_edge_nonneg_of_avoid_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryOpenPathPotential.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_repeated_boundary_edge_nonneg_of_avoid_east_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {d : FKMedialDart R.medialTorus}
  {w z : Int × Int}
-- given
  (heF : e ∉ F)
  (hcolor : fkMedialCheckerColor d = fkMedialCheckerColor (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))
  (havoid : ∀ k : Nat, let pairing := fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F) (fkMedialBoundaryStep pairing)^[k] d ≠ fkMedialEastDart (fkRectMedialVertexOfEdge R e)) :
-- imply
  let pairing := fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F) let c := fkRectRefinedBoundaryCanonicalCenter R d let n := orderOf (fkMedialBoundaryStep pairing) let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R) let U : Int × Int := (4 * (fkRectSquareDeckTranslation R w).1, 4 * (fkRectSquareDeckTranslation R w).2) let V : Int × Int := (4 * (fkRectSquareDeckTranslation R z).1, 4 * (fkRectSquareDeckTranslation R z).2) 0 ≤ fkRectRefinedRawInteraction ((fkRectRepeatTranslatedDartPath (fkRectRefinedBoundaryDarts pairing d c n) U L).map (fkRectIntegralSquareDartMod L)) ((fkRectRepeatTranslatedDartPath (fkRectRefinedPrimalEdgeDarts R e) V L).map (fkRectIntegralSquareDartMod L)) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_repeated_boundary_edge_nonneg_of_avoid_east R F e heF d w z hcolor havoid

/--
[FKRectRefinedOpenEdgeBlocks.boundary_interaction_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryOpenPathPotential.lean)
-/
@[path]
private lemma boundary_interaction_eq_zero_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {l : List FKRectIntegralSquareDart}
  {d : FKMedialDart R.medialTorus}
  {n : Nat}
  {w : Int × Int}
-- given
  (hl : FKRectRefinedOpenEdgeBlocks R F l) :
-- imply
  let pairing := fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F) let c := fkRectRefinedBoundaryCanonicalCenter R d let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R) let U : Int × Int := (4 * (fkRectSquareDeckTranslation R w).1, 4 * (fkRectSquareDeckTranslation R w).2) fkRectRefinedRawInteraction ((fkRectRepeatTranslatedDartPath (fkRectRefinedBoundaryDarts pairing d c n) U L).map (fkRectIntegralSquareDartMod L)) (l.map (fkRectIntegralSquareDartMod L)) = 0 := by
-- proof
  apply StatMech.FrontierD.FKRectRefinedOpenEdgeBlocks.boundary_interaction_eq_zero R F hl d n w


-- created on 2026-10-23
