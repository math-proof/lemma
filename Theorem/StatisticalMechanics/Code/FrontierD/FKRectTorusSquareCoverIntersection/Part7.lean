/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareCoverIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment.Part12
import Theorem.StatisticalMechanics.Code.FrontierD.IntegralSquareTorusIntersection.Part9
import Structure.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareCoverIntersection
open scoped BigOperators


namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

theorem FKRectIntegralSquareDartPath.exists_squareCoverCycleWitness
    (R : FKRectTorus) {p u : Int × Int}
    {l : List FKRectIntegralSquareDart}
    (h : FKRectIntegralSquareDartPath p
      (p.1 + u.1, p.2 + u.2) l) :
    Nonempty (FKRectSquareCoverCycleWitness R u) := by
  let L := fkRectSquareCoverSide R
  letI : Fact (2 < L) := ⟨fkRectSquareCoverSide_gt_two R⟩
  let repeated := fkRectRepeatTranslatedDartPath l u L
  have hrepeated : FKRectIntegralSquareDartPath p
      (p.1 + (L : Int) * u.1, p.2 + (L : Int) * u.2) repeated :=
    h.repeatTranslated L
  have hpointMod : fkRectIntegralSquarePointMod L p =
      fkRectIntegralSquarePointMod L
        (p.1 + (L : Int) * u.1, p.2 + (L : Int) * u.2) := by
    apply Prod.ext <;> simp [fkRectIntegralSquarePointMod]
  let darts := repeated.map (fkRectIntegralSquareDartMod L)
  have hbalanced : IntegralSquareTorusCycle.DartListBalanced darts := by
    exact hrepeated.dartListBalanced_of_pointMod_eq L hpointMod
  have hxEquation := hrepeated.displacement_x_eq_wrap (L := L)
  have hyEquation := hrepeated.displacement_y_eq_wrap (L := L)
  rw [hpointMod] at hxEquation hyEquation
  simp only [sub_self, zero_add] at hxEquation hyEquation
  rw [add_sub_cancel_left] at hxEquation hyEquation
  have hL : (L : Int) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_trans (by norm_num : 0 < 2)
      (fkRectSquareCoverSide_gt_two R)))
  have hxWrap :
      (darts.map ons_xWrapSign).sum = u.1 := by
    have hxScaled : (L : Int) * (darts.map ons_xWrapSign).sum =
        (L : Int) * u.1 := by
      dsimp [darts]
      exact hxEquation.symm
    exact mul_left_cancel₀ hL hxScaled
  have hyWrap :
      (darts.map ons_yWrapSign).sum = u.2 := by
    have hyScaled : (L : Int) * (darts.map ons_yWrapSign).sum =
        (L : Int) * u.2 := by
      dsimp [darts]
      exact hyEquation.symm
    exact mul_left_cancel₀ hL hyScaled
  let C := IntegralSquareTorusCycle.ofDartList darts hbalanced
  refine ⟨⟨C, ?_, ?_⟩⟩
  · rw [IntegralSquareTorusCycle.ofDartList_xFlux, hxWrap]
  · rw [IntegralSquareTorusCycle.ofDartList_yFlux, hyWrap]


theorem FKRectSquareWalkLift.exists_squareCoverCycleWitness
    (R : FKRectTorus) {G : SimpleGraph R.Vertex} {x : R.Vertex}
    {w : G.Walk x x} {p q : Int × Int}
    (h : FKRectSquareWalkLift R w p q) :
    Nonempty (FKRectSquareCoverCycleWitness R
      (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p)) := by
  obtain ⟨l, hl, hlen⟩ := h.exists_integralDartPath R
  have hend : fkRectSquareDevelopPoint q =
      ((fkRectSquareDevelopPoint p).1 +
          (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p).1,
        (fkRectSquareDevelopPoint p).2 +
          (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p).2) := by
    apply Prod.ext <;> simp
  rw [hend] at hl
  exact hl.exists_squareCoverCycleWitness R


theorem FKRectSquareCoverCycleWitness.not_independent_of_locallyDisjoint
    {R : FKRectTorus} {u v : Int × Int}
    (C : FKRectSquareCoverCycleWitness R u)
    (D : FKRectSquareCoverCycleWitness R v)
    (hdisj : C.cycle.LocallyDisjoint D.cycle) :
    ¬ FKRectWindingIndependent u v := by
  intro hind
  apply hind
  have hdet :=
    IntegralSquareTorusCycle.flux_det_eq_zero_of_locallyDisjoint hdisj
  rw [C.xFlux_eq, C.yFlux_eq, D.xFlux_eq, D.yFlux_eq] at hdet
  exact hdet


theorem FKRectSquareWalkLift.not_windingIndependent_of_locallyDisjoint
    (R : FKRectTorus)
    {G H : SimpleGraph R.Vertex} {x y : R.Vertex}
    {w : G.Walk x x} {z : H.Walk y y}
    {p q a b : Int × Int}
    (hw : FKRectSquareWalkLift R w p q)
    (hz : FKRectSquareWalkLift R z a b)
    (C : FKRectSquareCoverCycleWitness R
      (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p))
    (D : FKRectSquareCoverCycleWitness R
      (fkRectSquareDevelopPoint b - fkRectSquareDevelopPoint a))
    (hdisj : C.cycle.LocallyDisjoint D.cycle) :
    ¬ FKRectWindingIndependent
      (fkRectWalkWinding R w) (fkRectWalkWinding R z) := by
  intro hind
  apply C.not_independent_of_locallyDisjoint D hdisj
  exact (hw.closed_developedIndependent_iff R hz).mpr hind

end
end StatMech.FrontierD
