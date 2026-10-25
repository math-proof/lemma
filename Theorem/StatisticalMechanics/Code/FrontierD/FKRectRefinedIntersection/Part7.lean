/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedInteractionCore.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectRefinedIntersection.Part6
open scoped BigOperators
open Finset


namespace StatMech.FrontierD

open StatMech.Onsager

open IntegralSquareTorusCycle

noncomputable section

variable {L : Nat} [Fact (8 < L)]

theorem fkRectRefinedBoundaryOrbit_exists_squareCoverCycleWitness
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialDart R.medialTorus) (c : Int × Int) :
    Nonempty (FKRectSquareCoverCycleWitness R
      (fkRectRefinedBoundaryOrbitTranslation pairing d c)) := by
  let n := orderOf (fkMedialBoundaryStep pairing)
  let c' := fkRectRefinedBoundaryCenterAfter pairing d c n
  let u := fkRectRefinedBoundaryOrbitTranslation pairing d c
  have hpath := fkRectRefinedBoundaryOrbitDarts_path pairing d c
  change FKRectIntegralSquareDartPath
      (fkRectRefinedDartPoint c d.2)
      (fkRectRefinedDartPoint c' d.2)
      (fkRectRefinedBoundaryDarts pairing d c n) at hpath
  have hend : fkRectRefinedDartPoint c' d.2 =
      ((fkRectRefinedDartPoint c d.2).1 + u.1,
        (fkRectRefinedDartPoint c d.2).2 + u.2) := by
    unfold fkRectRefinedDartPoint u
      fkRectRefinedBoundaryOrbitTranslation c' n
    apply Prod.ext <;> simp <;> ring
  rw [hend] at hpath
  exact hpath.exists_squareCoverCycleWitness R


theorem fkRectRefinedBoundaryOrbit_exists_largeCoverCycleWitness
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialDart R.medialTorus) (c : Int × Int) :
    Nonempty (FKRectSquareCoverCycleWitness (fkRectRefinedCoverTorus R)
      (fkRectRefinedBoundaryOrbitTranslation pairing d c)) := by
  let n := orderOf (fkMedialBoundaryStep pairing)
  let c' := fkRectRefinedBoundaryCenterAfter pairing d c n
  let u := fkRectRefinedBoundaryOrbitTranslation pairing d c
  have hpath := fkRectRefinedBoundaryOrbitDarts_path pairing d c
  change FKRectIntegralSquareDartPath
      (fkRectRefinedDartPoint c d.2)
      (fkRectRefinedDartPoint c' d.2)
      (fkRectRefinedBoundaryDarts pairing d c n) at hpath
  have hend : fkRectRefinedDartPoint c' d.2 =
      ((fkRectRefinedDartPoint c d.2).1 + u.1,
        (fkRectRefinedDartPoint c d.2).2 + u.2) := by
    unfold fkRectRefinedDartPoint u
      fkRectRefinedBoundaryOrbitTranslation c' n
    apply Prod.ext <;> simp <;> ring
  rw [hend] at hpath
  exact hpath.exists_squareCoverCycleWitness (fkRectRefinedCoverTorus R)


theorem fkRectMedialBoundaryPrimalOrbitWalk_winding
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) :
    fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega d) =
      fkRectMedialBoundaryPrimalSeamTrace R
        (fkRectConfigurationToMedialPairing R omega) d
        (orderOf (fkMedialBoundaryStep
          (fkRectConfigurationToMedialPairing R omega))) := by
  unfold fkRectMedialBoundaryPrimalOrbitWalk
  rw [fkRectWalkWinding_copy]
  exact fkRectMedialBoundaryPrimalTrace_winding R omega d _


theorem fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) :
    fkRectRefinedBoundaryOrbitTranslation
        (fkRectConfigurationToMedialPairing R omega) d
        (fkRectRefinedBoundaryCanonicalCenter R d) =
      (4 * (fkRectSquareDeckTranslation R
        (fkRectWalkWinding R
          (fkRectMedialBoundaryPrimalOrbitWalk R omega d))).1,
       4 * (fkRectSquareDeckTranslation R
        (fkRectWalkWinding R
          (fkRectMedialBoundaryPrimalOrbitWalk R omega d))).2) := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  let n := orderOf (fkMedialBoundaryStep pairing)
  have hc := fkRectRefinedBoundaryCenterAfter_eq_canonical_add_deck
    R pairing d (0, 0) n
  simp only [add_zero] at hc
  have hpow : (fkMedialBoundaryStep pairing) ^ n = 1 :=
    pow_orderOf_eq_one _
  have hret : (fkMedialBoundaryStep pairing)^[n] d = d := by
    rw [← Equiv.Perm.coe_pow]
    simpa [hpow]
  rw [hret] at hc
  have hw : fkRectWalkWinding R
      (fkRectMedialBoundaryPrimalOrbitWalk R omega d) =
        fkRectMedialBoundaryPrimalSeamTrace R pairing d n := by
    dsimp [pairing, n]
    exact fkRectMedialBoundaryPrimalOrbitWalk_winding R omega d
  rw [hw]
  unfold fkRectRefinedBoundaryOrbitTranslation
  dsimp [pairing, n] at hc ⊢
  have hc1 := congrArg Prod.fst hc
  have hc2 := congrArg Prod.snd hc
  apply Prod.ext
  · simp only [Prod.fst, Prod.snd] at hc1 ⊢
    rw [hc1]
    ring
  · simp only [Prod.fst, Prod.snd] at hc2 ⊢
    rw [hc2]
    ring


theorem fkRectRefinedBoundaryOrbit_exists_canonicalWindingWitness
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) :
    Nonempty (FKRectSquareCoverCycleWitness R
      (4 * (fkRectSquareDeckTranslation R
        (fkRectWalkWinding R
          (fkRectMedialBoundaryPrimalOrbitWalk R omega d))).1,
       4 * (fkRectSquareDeckTranslation R
        (fkRectWalkWinding R
          (fkRectMedialBoundaryPrimalOrbitWalk R omega d))).2)) := by
  rw [← fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding]
  exact fkRectRefinedBoundaryOrbit_exists_squareCoverCycleWitness R
    (fkRectConfigurationToMedialPairing R omega) d
    (fkRectRefinedBoundaryCanonicalCenter R d)


theorem fkRectRefinedBoundaryOrbit_exists_largeCanonicalWindingWitness
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) :
    Nonempty (FKRectSquareCoverCycleWitness (fkRectRefinedCoverTorus R)
      (4 * (fkRectSquareDeckTranslation R
        (fkRectWalkWinding R
          (fkRectMedialBoundaryPrimalOrbitWalk R omega d))).1,
       4 * (fkRectSquareDeckTranslation R
        (fkRectWalkWinding R
          (fkRectMedialBoundaryPrimalOrbitWalk R omega d))).2)) := by
  rw [← fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding]
  exact fkRectRefinedBoundaryOrbit_exists_largeCoverCycleWitness R
    (fkRectConfigurationToMedialPairing R omega) d
    (fkRectRefinedBoundaryCanonicalCenter R d)


theorem fkRectMedialBoundaryPrimalOrbitWalk_windingIndependent_of_intersection
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus)
    {G : SimpleGraph R.Vertex} {x : R.Vertex}
    {w : G.Walk x x} {p q : Int × Int}
    (hw : FKRectSquareWalkLift R w p q)
    (C : FKRectSquareCoverCycleWitness R
      (fkRectRefinedBoundaryOrbitTranslation
        (fkRectConfigurationToMedialPairing R omega) d
        (fkRectRefinedBoundaryCanonicalCenter R d)))
    (D : FKRectSquareCoverCycleWitness R
      (4 * (fkRectSquareDevelopPoint q -
          fkRectSquareDevelopPoint p).1,
        4 * (fkRectSquareDevelopPoint q -
          fkRectSquareDevelopPoint p).2))
    (hne : C.cycle.intersection D.cycle ≠ 0) :
    FKRectWindingIndependent
      (fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega d))
      (fkRectWalkWinding R w) := by
  have hscaled := C.windingIndependent_of_intersection_ne_zero D hne
  rw [fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding,
    hw.closed_develop_sub_eq_deck_winding R] at hscaled
  exact (fkRectWindingIndependent_four_squareDeck_iff R _ _).mp hscaled


theorem fkRectMedialBoundaryPrimalOrbitWalk_windingIndependent_of_largeIntersection
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus)
    {G : SimpleGraph R.Vertex} {x : R.Vertex}
    {w : G.Walk x x} {p q : Int × Int}
    (hw : FKRectSquareWalkLift R w p q)
    (C : FKRectSquareCoverCycleWitness (fkRectRefinedCoverTorus R)
      (fkRectRefinedBoundaryOrbitTranslation
        (fkRectConfigurationToMedialPairing R omega) d
        (fkRectRefinedBoundaryCanonicalCenter R d)))
    (D : FKRectSquareCoverCycleWitness (fkRectRefinedCoverTorus R)
      (4 * (fkRectSquareDevelopPoint q -
          fkRectSquareDevelopPoint p).1,
        4 * (fkRectSquareDevelopPoint q -
          fkRectSquareDevelopPoint p).2))
    (hne : C.cycle.intersection D.cycle ≠ 0) :
    FKRectWindingIndependent
      (fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega d))
      (fkRectWalkWinding R w) := by
  have hscaled := C.windingIndependent_of_intersection_ne_zero D hne
  rw [fkRectRefinedBoundaryOrbitTranslation_eq_four_deck_winding,
    hw.closed_develop_sub_eq_deck_winding R] at hscaled
  exact (fkRectWindingIndependent_four_squareDeck_iff R _ _).mp hscaled

end
end StatMech.FrontierD
