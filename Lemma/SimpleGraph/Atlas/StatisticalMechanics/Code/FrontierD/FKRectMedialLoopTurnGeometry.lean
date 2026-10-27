import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialLoopTurnGeometry.Part3
open StatMech StatMech.FrontierD


/--
[fkRectClosedPairing_eq_not_vertexParity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnGeometry.lean)
-/
@[path]
private lemma fkRectClosedPairing_eq_not_vertexParity_eq
  {R : FKRectTorus}
  {v : R.medialTorus.Vertex} :
-- imply
  fkRectClosedPairingAtEdge (fkRectTorusMedialEdgeEquiv R v) = !fkMedialVertexParity v := by
-- proof
  apply StatMech.FrontierD.fkRectClosedPairing_eq_not_vertexParity R v

/--
[fkRectBlackDartShiftedSite_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnGeometry.lean)
-/
@[path]
private lemma fkRectBlackDartShiftedSite_zero_eq
  {R : FKRectTorus}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  fkRectBlackDartShiftedSite R (0, 0) d = fkRectBlackDartSite R d := by
-- proof
  apply StatMech.FrontierD.fkRectBlackDartShiftedSite_zero R d

/--
[fkRectRefinedDartSite_reduce_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnGeometry.lean)
-/
@[path]
private lemma fkRectRefinedDartSite_reduce_four_eq
  {L : Nat}
  {c : Int × Int}
  {side : FKMedialSide}
-- given
  (h4 : 4 ∣ L)
  (horizontal : Bool)
  (hc : FKRectRefinedEdgeCenterNormal horizontal c) :
-- imply
  (ZMod.castHom h4 (ZMod 4) (fkRectIntegralSquarePointMod L (fkRectRefinedDartPoint c side)).1, ZMod.castHom h4 (ZMod 4) (fkRectIntegralSquarePointMod L (fkRectRefinedDartPoint c side)).2) = fkRectRefinedDartResidue horizontal side := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedDartSite_reduce_four h4 horizontal c side hc

/--
[fkRectRefinedDartResidue_injective_of_blackSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnGeometry.lean)
-/
@[path]
private lemma fkRectRefinedDartResidue_injective_of_blackSide_eq
  {p q : Bool}
  {s t : FKMedialSide}
-- given
  (hs : fkMedialSideVertical s = !p)
  (ht : fkMedialSideVertical t = !q)
  (h : fkRectRefinedDartResidue p s = fkRectRefinedDartResidue q t) :
-- imply
  p = q ∧ s = t := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedDartResidue_injective_of_blackSide p q s t hs ht h

/--
[fkRectBlackDart_sideVertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnGeometry.lean)
-/
@[path]
private lemma fkRectBlackDart_sideVertical_eq
  {R : FKRectTorus}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  fkMedialSideVertical d.1.2 = !fkRectClosedPairingAtEdge (fkRectTorusMedialEdgeEquiv R d.1.1) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackDart_sideVertical R d

/--
[fkRectBlackDartSite_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnGeometry.lean)
-/
@[path]
private lemma fkRectBlackDartSite_injective_eq
  {R : FKRectTorus} :
-- imply
  Function.Injective (fkRectBlackDartSite R) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackDartSite_injective R

/--
[fkRectBlackDart_eq_of_shiftedSite_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnGeometry.lean)
-/
@[path]
private lemma fkRectBlackDart_eq_of_shiftedSite_eq_eq
  {R : FKRectTorus}
  {u : Int × Int}
  {d e : FKMedialBlackDart R.medialTorus}
-- given
  (hsite : fkRectBlackDartShiftedSite R u d = fkRectBlackDartSite R e) :
-- imply
  d = e := by
-- proof
  apply StatMech.FrontierD.fkRectBlackDart_eq_of_shiftedSite_eq R u d e hsite

/--
[fkRectBlackDart_eq_of_shiftedSite_eq_shiftedSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnGeometry.lean)
-/
@[path]
private lemma fkRectBlackDart_eq_of_shiftedSite_eq_shiftedSite_eq
  {R : FKRectTorus}
  {u v : Int × Int}
  {d e : FKMedialBlackDart R.medialTorus}
-- given
  (hsite : fkRectBlackDartShiftedSite R u d = fkRectBlackDartShiftedSite R v e) :
-- imply
  d = e := by
-- proof
  apply StatMech.FrontierD.fkRectBlackDart_eq_of_shiftedSite_eq_shiftedSite R u v d e hsite

/--
[fkRectBlackDartShiftedPoint_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnGeometry.lean)
-/
@[path]
private lemma fkRectBlackDartShiftedPoint_injective_eq
  {R : FKRectTorus} :
-- imply
  Function.Injective (fun z : (Int × Int) × FKMedialBlackDart R.medialTorus => fkRectBlackDartShiftedPoint R z.1 z.2) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackDartShiftedPoint_injective R

/--
[fkRectRefinedDartPoint_localMate_eq_add_two_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnGeometry.lean)
-/
@[path]
private lemma fkRectRefinedDartPoint_localMate_eq_add_two_step_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialDart T}
  {c : Int × Int} :
-- imply
  fkRectRefinedDartPoint c (fkMedialLocalMate pairing d).2 = ((fkRectRefinedDartPoint c d.2).1 + 2 * StatMech.Onsager.ons_dirExponentX (fkMedialStrandDirection pairing d), (fkRectRefinedDartPoint c d.2).2 + 2 * StatMech.Onsager.ons_dirExponentY (fkMedialStrandDirection pairing d)) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedDartPoint_localMate_eq_add_two_step pairing d c

/--
[fkRectRefinedBoundaryStep_point](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnGeometry.lean)
-/
@[path]
private lemma fkRectRefinedBoundaryStep_point_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialDart T}
  {c : Int × Int} :
-- imply
  fkRectRefinedDartPoint (fkRectRefinedBondCenter c (fkMedialLocalMate pairing d).2) (fkMedialBoundaryStep pairing d).2 = ((fkRectRefinedDartPoint c d.2).1 + 2 * StatMech.Onsager.ons_dirExponentX (fkMedialStrandDirection pairing d), (fkRectRefinedDartPoint c d.2).2 + 2 * StatMech.Onsager.ons_dirExponentY (fkMedialStrandDirection pairing d)) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedBoundaryStep_point pairing d c


-- created on 2026-10-23
