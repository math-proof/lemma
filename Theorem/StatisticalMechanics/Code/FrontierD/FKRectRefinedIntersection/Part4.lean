/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedInteractionCore.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectRefinedIntersection.Part3
open scoped BigOperators
open Finset


namespace StatMech.FrontierD

open StatMech.Onsager

open IntegralSquareTorusCycle

noncomputable section

variable {L : Nat} [Fact (8 < L)]

theorem FKRectIntegralSquareDartPath.refinedScale
    {p q : Int × Int} {l : List FKRectIntegralSquareDart}
    (h : FKRectIntegralSquareDartPath p q l) :
    FKRectIntegralSquareDartPath
      (fkRectRefinedScalePoint p) (fkRectRefinedScalePoint q)
      (fkRectRefinedScaleDarts l) := by
  induction h with
  | nil p => exact FKRectIntegralSquareDartPath.nil _
  | @cons d q r l hend tail ih =>
      unfold fkRectRefinedScaleDarts
      rw [List.flatMap_cons]
      have hd := fkRectRefinedScaleDart_path d
      rw [hend] at hd
      exact hd.append ih


theorem FKRectSquareWalkLift.exists_refinedDartPath
    (R : FKRectTorus) {G : SimpleGraph R.Vertex}
    {x y : R.Vertex} {w : G.Walk x y} {p q : Int × Int}
    (h : FKRectSquareWalkLift R w p q) :
    ∃ l : List FKRectIntegralSquareDart,
      FKRectIntegralSquareDartPath
        (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p))
        (fkRectRefinedScalePoint (fkRectSquareDevelopPoint q)) l := by
  obtain ⟨l, hl, -⟩ := h.exists_integralDartPath R
  exact ⟨fkRectRefinedScaleDarts l, hl.refinedScale⟩


theorem FKRectSquareWalkLift.exists_refinedSquareCoverCycleWitness
    (R : FKRectTorus) {G : SimpleGraph R.Vertex}
    {x : R.Vertex} {w : G.Walk x x} {p q : Int × Int}
    (h : FKRectSquareWalkLift R w p q) :
    Nonempty (FKRectSquareCoverCycleWitness R
      (4 * (fkRectSquareDevelopPoint q -
          fkRectSquareDevelopPoint p).1,
        4 * (fkRectSquareDevelopPoint q -
          fkRectSquareDevelopPoint p).2)) := by
  obtain ⟨l, hl⟩ := h.exists_refinedDartPath R
  let u : Int × Int :=
    (4 * (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p).1,
      4 * (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p).2)
  have hend : fkRectRefinedScalePoint (fkRectSquareDevelopPoint q) =
      ((fkRectRefinedScalePoint (fkRectSquareDevelopPoint p)).1 + u.1,
        (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p)).2 + u.2) := by
    apply Prod.ext <;>
      simp [fkRectRefinedScalePoint, u] <;> ring
  rw [hend] at hl
  exact hl.exists_squareCoverCycleWitness R


theorem FKRectSquareWalkLift.exists_refinedLargeCoverCycleWitness
    (R : FKRectTorus) {G : SimpleGraph R.Vertex}
    {x : R.Vertex} {w : G.Walk x x} {p q : Int × Int}
    (h : FKRectSquareWalkLift R w p q) :
    Nonempty (FKRectSquareCoverCycleWitness (fkRectRefinedCoverTorus R)
      (4 * (fkRectSquareDevelopPoint q -
          fkRectSquareDevelopPoint p).1,
        4 * (fkRectSquareDevelopPoint q -
          fkRectSquareDevelopPoint p).2)) := by
  obtain ⟨l, hl⟩ := h.exists_refinedDartPath R
  let u : Int × Int :=
    (4 * (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p).1,
      4 * (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p).2)
  have hend : fkRectRefinedScalePoint (fkRectSquareDevelopPoint q) =
      ((fkRectRefinedScalePoint (fkRectSquareDevelopPoint p)).1 + u.1,
        (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p)).2 + u.2) := by
    apply Prod.ext <;>
      simp [fkRectRefinedScalePoint, u] <;> ring
  rw [hend] at hl
  exact hl.exists_squareCoverCycleWitness (fkRectRefinedCoverTorus R)


theorem FKRectSquareWalkLift.windingIndependent_of_refinedIntersection_ne_zero
    (R : FKRectTorus)
    {G H : SimpleGraph R.Vertex} {x y : R.Vertex}
    {w : G.Walk x x} {z : H.Walk y y}
    {p q a b : Int × Int}
    (hw : FKRectSquareWalkLift R w p q)
    (hz : FKRectSquareWalkLift R z a b)
    (C : FKRectSquareCoverCycleWitness R
      (4 * (fkRectSquareDevelopPoint q -
          fkRectSquareDevelopPoint p).1,
        4 * (fkRectSquareDevelopPoint q -
          fkRectSquareDevelopPoint p).2))
    (D : FKRectSquareCoverCycleWitness R
      (4 * (fkRectSquareDevelopPoint b -
          fkRectSquareDevelopPoint a).1,
        4 * (fkRectSquareDevelopPoint b -
          fkRectSquareDevelopPoint a).2))
    (hne : C.cycle.intersection D.cycle ≠ 0) :
    FKRectWindingIndependent
      (fkRectWalkWinding R w) (fkRectWalkWinding R z) := by
  have hscaled := C.windingIndependent_of_intersection_ne_zero D hne
  have hdeveloped : FKRectWindingIndependent
      (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p)
      (fkRectSquareDevelopPoint b - fkRectSquareDevelopPoint a) :=
    (fkRectWindingIndependent_four_iff _ _).mp hscaled
  exact (hw.closed_developedIndependent_iff R hz).mp hdeveloped


end
end StatMech.FrontierD
