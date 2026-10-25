/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedOrbitInteraction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedInteractionCore.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryOrbitVisits.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectRefinedOrbitInteraction.Part2
open scoped BigOperators
open Equiv Finset


namespace StatMech.FrontierD

noncomputable section

theorem fkRectRefinedRawInteraction_boundaryDarts
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialDart R.medialTorus) (c : Int × Int)
    (e : R.EdgeIndex) (n : Nat) :
    fkRectRefinedRawInteraction
        ((fkRectRefinedBoundaryDarts pairing d c n).map
          (fkRectIntegralSquareDartMod
            (fkRectSquareCoverSide (fkRectRefinedCoverTorus R))))
        ((fkRectRefinedPrimalEdgeDarts R e).map
          (fkRectIntegralSquareDartMod
            (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) =
      fkRectRefinedBoundaryInteractionTrace R pairing e d c n := by
  induction n generalizing d c with
  | zero => simp [fkRectRefinedBoundaryDarts,
      fkRectRefinedBoundaryInteractionTrace,
      fkRectRefinedRawInteraction]
  | succ n ih =>
      simp only [fkRectRefinedBoundaryDarts,
        List.map_append, fkRectRefinedRawInteraction_append_left,
        fkRectRefinedBoundaryInteractionTrace]
      rw [ih]
      rfl


theorem fkRectRefinedBoundaryInteractionTrace_eq_signedVisits
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (e : R.EdgeIndex) (a b d : FKMedialDart R.medialTorus)
    (c : Int × Int) (n : Nat)
    (hlocal : forall (d' : FKMedialDart R.medialTorus) (c' : Int × Int),
      fkRectRefinedBoundaryLocalInteraction R pairing d' c' e =
        (if d' = a then 1 else 0) - (if d' = b then 1 else 0)) :
    fkRectRefinedBoundaryInteractionTrace R pairing e d c n =
      permOrbitSignedVisitTrace (fkMedialBoundaryStep pairing) d a b n := by
  induction n generalizing d c with
  | zero => simp [fkRectRefinedBoundaryInteractionTrace,
      permOrbitSignedVisitTrace]
  | succ n ih =>
      rw [fkRectRefinedBoundaryInteractionTrace,
        permOrbitSignedVisitTrace, hlocal, ih]


theorem fkRectRefinedBoundaryInteractionTrace_eq_signedVisits_of_hasLocal
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (e : R.EdgeIndex) (a b d : FKMedialDart R.medialTorus)
    (c : Int × Int) (n : Nat)
    (hlocal : FKRectRefinedBoundaryHasLocalVisitInteraction
      R pairing e a b d c n) :
    fkRectRefinedBoundaryInteractionTrace R pairing e d c n =
      permOrbitSignedVisitTrace (fkMedialBoundaryStep pairing) d a b n := by
  induction n generalizing d c with
  | zero => simp [fkRectRefinedBoundaryInteractionTrace,
      permOrbitSignedVisitTrace]
  | succ n ih =>
      rcases hlocal with ⟨hone, htail⟩
      rw [fkRectRefinedBoundaryInteractionTrace,
        permOrbitSignedVisitTrace, hone, ih _ _ htail]


theorem fkRectRefinedRawInteraction_boundaryOrbit_eq_visitCount_sub
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (e : R.EdgeIndex) (a b d : FKMedialDart R.medialTorus)
    (c : Int × Int)
    (hlocal : forall (d' : FKMedialDart R.medialTorus) (c' : Int × Int),
      fkRectRefinedBoundaryLocalInteraction R pairing d' c' e =
        (if d' = a then 1 else 0) - (if d' = b then 1 else 0)) :
    fkRectRefinedRawInteraction
        ((fkRectRefinedBoundaryDarts pairing d c
            (orderOf (fkMedialBoundaryStep pairing))).map
          (fkRectIntegralSquareDartMod
            (fkRectSquareCoverSide (fkRectRefinedCoverTorus R))))
        ((fkRectRefinedPrimalEdgeDarts R e).map
          (fkRectIntegralSquareDartMod
            (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) =
      (fkMedialBoundaryOrbitVisitCount pairing d a : Int) -
        fkMedialBoundaryOrbitVisitCount pairing d b := by
  rw [fkRectRefinedRawInteraction_boundaryDarts]
  rw [fkRectRefinedBoundaryInteractionTrace_eq_signedVisits
    R pairing e a b d c _ hlocal]
  exact permOrbitSignedVisitTrace_orderOf _ _ _ _


theorem fkRectRefinedRawInteraction_boundaryOrbit_eq_visitCount_sub_of_hasLocal
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (e : R.EdgeIndex) (a b d : FKMedialDart R.medialTorus)
    (c : Int × Int)
    (hlocal : FKRectRefinedBoundaryHasLocalVisitInteraction R pairing e a b
      d c (orderOf (fkMedialBoundaryStep pairing))) :
    fkRectRefinedRawInteraction
        ((fkRectRefinedBoundaryDarts pairing d c
            (orderOf (fkMedialBoundaryStep pairing))).map
          (fkRectIntegralSquareDartMod
            (fkRectSquareCoverSide (fkRectRefinedCoverTorus R))))
        ((fkRectRefinedPrimalEdgeDarts R e).map
          (fkRectIntegralSquareDartMod
            (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) =
      (fkMedialBoundaryOrbitVisitCount pairing d a : Int) -
        fkMedialBoundaryOrbitVisitCount pairing d b := by
  rw [fkRectRefinedRawInteraction_boundaryDarts]
  rw [fkRectRefinedBoundaryInteractionTrace_eq_signedVisits_of_hasLocal
    R pairing e a b d c _ hlocal]
  exact permOrbitSignedVisitTrace_orderOf _ _ _ _

end
end StatMech.FrontierD
