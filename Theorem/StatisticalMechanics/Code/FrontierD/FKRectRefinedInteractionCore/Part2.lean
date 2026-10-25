/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedInteractionCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedBoundary.Part4
import Instance.StatisticalMechanics.Code.FrontierD.FKRectRefinedInteractionCore
open scoped BigOperators
open Finset


namespace StatMech.FrontierD

open StatMech.Onsager

open IntegralSquareTorusCycle

noncomputable section

theorem FKRectSquareCoverCycleWitness.windingIndependent_of_intersection_ne_zero
    {R : FKRectTorus} {u v : Int × Int}
    (C : FKRectSquareCoverCycleWitness R u)
    (D : FKRectSquareCoverCycleWitness R v)
    (hne : C.cycle.intersection D.cycle ≠ 0) :
    FKRectWindingIndependent u v := by
  unfold FKRectWindingIndependent
  intro hdet
  apply hne
  rw [C.cycle.intersection_eq_flux_det D.cycle,
    C.xFlux_eq, C.yFlux_eq, D.xFlux_eq, D.yFlux_eq, hdet]

theorem fkRectWindingIndependent_four_iff (u v : Int × Int) :
    FKRectWindingIndependent (4 * u.1, 4 * u.2)
        (4 * v.1, 4 * v.2) <->
      FKRectWindingIndependent u v := by
  unfold FKRectWindingIndependent
  constructor
  · intro h hz
    apply h
    linear_combination 16 * hz
  · intro h hs
    apply h
    have hscaled : (16 : Int) * (u.1 * v.2 - u.2 * v.1) = 0 := by
      linear_combination hs
    exact (mul_eq_zero.mp hscaled).resolve_left (by norm_num)

theorem fkRectWindingIndependent_four_squareDeck_iff
    (R : FKRectTorus) (u v : Int × Int) :
    FKRectWindingIndependent
        (4 * (fkRectSquareDeckTranslation R u).1,
          4 * (fkRectSquareDeckTranslation R u).2)
        (4 * (fkRectSquareDeckTranslation R v).1,
          4 * (fkRectSquareDeckTranslation R v).2) <->
      FKRectWindingIndependent u v := by
  rw [fkRectWindingIndependent_four_iff,
    fkRectWindingIndependent_squareDeck_iff]

theorem not_windingIndependent_trans_of_middle_ne_zero
    (u b v : Int × Int) (hb : b ≠ (0, 0))
    (hub : ¬ FKRectWindingIndependent u b)
    (hbv : ¬ FKRectWindingIndependent b v) :
    ¬ FKRectWindingIndependent u v := by
  unfold FKRectWindingIndependent at hub hbv ⊢
  simp only [not_ne_iff] at hub hbv ⊢
  have hcoord : b.1 ≠ 0 ∨ b.2 ≠ 0 := by
    by_contra h
    push Not at h
    exact hb (Prod.ext h.1 h.2)
  rcases hcoord with hb1 | hb2
  · have hmul : b.1 * (u.1 * v.2 - u.2 * v.1) = 0 := by
      linear_combination u.1 * hbv + v.1 * hub
    exact (mul_eq_zero.mp hmul).resolve_left hb1
  · have hmul : b.2 * (u.1 * v.2 - u.2 * v.1) = 0 := by
      linear_combination v.2 * hub + u.2 * hbv
    exact (mul_eq_zero.mp hmul).resolve_left hb2

end
end StatMech.FrontierD
