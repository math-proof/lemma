import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectRefinedBoundaryVisitSupport
open Finset StatMech StatMech.FrontierD


/--
[fkMedialDart_eq_west_or_east_of_vertex_eq_of_checkerColor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryVisitSupport.lean)
-/
@[path]
private lemma fkMedialDart_eq_west_or_east_of_vertex_eq_of_checkerColor_eq
  {T : EvenTorus}
  {d : FKMedialDart T}
  {v : T.Vertex}
-- given
  (hvertex : d.1 = v)
  (hcolor : fkMedialCheckerColor d = fkMedialCheckerColor (fkMedialWestDart v)) :
-- imply
  d = fkMedialWestDart v ∨ d = fkMedialEastDart v := by
-- proof
  apply StatMech.FrontierD.fkMedialDart_eq_west_or_east_of_vertex_eq_of_checkerColor d v hvertex hcolor

/--
[fkRectConfigurationOfEdges_pairing_eq_closed_or_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryVisitSupport.lean)
-/
@[path]
private lemma fkRectConfigurationOfEdges_pairing_eq_closed_or_open_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {d : FKMedialDart R.medialTorus} :
-- imply
  let f := fkRectTorusMedialEdgeEquiv R d.1 fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F) d.1 = if f ∈ F then !fkRectClosedPairingAtEdge f else fkRectClosedPairingAtEdge f := by
-- proof
  apply StatMech.FrontierD.fkRectConfigurationOfEdges_pairing_eq_closed_or_open R F d

/--
[fkRectRefinedBondCenter_exists_deck](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryVisitSupport.lean)
-/
@[path]
private lemma fkRectRefinedBondCenter_exists_deck_eq
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {d : FKMedialDart R.medialTorus}
  {c : Int × Int}
  {u : Int × Int}
-- given
  (hcenter : c = ((fkRectRefinedBoundaryCanonicalCenter R d).1 + 4 * (fkRectSquareDeckTranslation R u).1, (fkRectRefinedBoundaryCanonicalCenter R d).2 + 4 * (fkRectSquareDeckTranslation R u).2)) :
-- imply
  ∃ v : Int × Int, fkRectRefinedBondCenter c (fkMedialLocalMate pairing d).2 = ((fkRectRefinedBoundaryCanonicalCenter R (fkMedialBoundaryStep pairing d)).1 + 4 * (fkRectSquareDeckTranslation R v).1, (fkRectRefinedBoundaryCanonicalCenter R (fkMedialBoundaryStep pairing d)).2 + 4 * (fkRectSquareDeckTranslation R v).2) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedBondCenter_exists_deck R pairing d c u hcenter

/--
[fkRectRefinedBoundaryLocalInteraction_eq_signedVisit_of_color](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryVisitSupport.lean)
-/
@[path]
private lemma fkRectRefinedBoundaryLocalInteraction_eq_signedVisit_of_color_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {d : FKMedialDart R.medialTorus}
  {c : Int × Int}
  {u : Int × Int}
-- given
  (heF : e ∉ F)
  (hcolor : fkMedialCheckerColor d = fkMedialCheckerColor (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))
  (hcenter : c = ((fkRectRefinedBoundaryCanonicalCenter R d).1 + 4 * (fkRectSquareDeckTranslation R u).1, (fkRectRefinedBoundaryCanonicalCenter R d).2 + 4 * (fkRectSquareDeckTranslation R u).2)) :
-- imply
  let pairing := fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F) let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R) fkRectRefinedBoundaryLocalInteraction R pairing d c e = if fkRectTorusMedialEdgeEquiv R d.1 = e ∧ (((c.1 : Int) : ZMod L), ((c.2 : Int) : ZMod L)) = ((((fkRectRefinedPrimalEdgeCenter R e).1 : Int) : ZMod L), (((fkRectRefinedPrimalEdgeCenter R e).2 : Int) : ZMod L)) then if d = fkMedialWestDart (fkRectMedialVertexOfEdge R e) then 1 else -1 else 0 := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedBoundaryLocalInteraction_eq_signedVisit_of_color R F e heF d c u hcolor hcenter

/--
[fkRectRefinedBoundaryLocalInteraction_eq_zero_of_target_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryVisitSupport.lean)
-/
@[path]
private lemma fkRectRefinedBoundaryLocalInteraction_eq_zero_of_target_mem_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {d : FKMedialDart R.medialTorus}
  {c : Int × Int}
  {u : Int × Int}
-- given
  (heF : e ∈ F)
  (hcenter : c = ((fkRectRefinedBoundaryCanonicalCenter R d).1 + 4 * (fkRectSquareDeckTranslation R u).1, (fkRectRefinedBoundaryCanonicalCenter R d).2 + 4 * (fkRectSquareDeckTranslation R u).2)) :
-- imply
  let pairing := fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F) fkRectRefinedBoundaryLocalInteraction R pairing d c e = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedBoundaryLocalInteraction_eq_zero_of_target_mem R F e heF d c u hcenter

/--
[fkRectRefinedBoundaryInteractionTrace_eq_zero_of_target_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryVisitSupport.lean)
-/
@[path]
private lemma fkRectRefinedBoundaryInteractionTrace_eq_zero_of_target_mem_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {d : FKMedialDart R.medialTorus}
  {c : Int × Int}
  {u : Int × Int}
  {n : Nat}
-- given
  (heF : e ∈ F)
  (hcenter : c = ((fkRectRefinedBoundaryCanonicalCenter R d).1 + 4 * (fkRectSquareDeckTranslation R u).1, (fkRectRefinedBoundaryCanonicalCenter R d).2 + 4 * (fkRectSquareDeckTranslation R u).2)) :
-- imply
  let pairing := fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F) fkRectRefinedBoundaryInteractionTrace R pairing e d c n = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedBoundaryInteractionTrace_eq_zero_of_target_mem R F e heF d c u n hcenter

/--
[fkRectRefinedBoundaryInteractionTrace_eq_matchedVisits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryVisitSupport.lean)
-/
@[path]
private lemma fkRectRefinedBoundaryInteractionTrace_eq_matchedVisits_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {d : FKMedialDart R.medialTorus}
  {c : Int × Int}
  {u : Int × Int}
  {n : Nat}
-- given
  (heF : e ∉ F)
  (hcolor : fkMedialCheckerColor d = fkMedialCheckerColor (fkMedialWestDart (fkRectMedialVertexOfEdge R e)))
  (hcenter : c = ((fkRectRefinedBoundaryCanonicalCenter R d).1 + 4 * (fkRectSquareDeckTranslation R u).1, (fkRectRefinedBoundaryCanonicalCenter R d).2 + 4 * (fkRectSquareDeckTranslation R u).2)) :
-- imply
  let pairing := fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F) fkRectRefinedBoundaryInteractionTrace R pairing e d c n = fkRectRefinedBoundaryMatchedVisitTrace R pairing e d c n := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedBoundaryInteractionTrace_eq_matchedVisits R F e heF d c u n hcolor hcenter


-- created on 2026-10-23
