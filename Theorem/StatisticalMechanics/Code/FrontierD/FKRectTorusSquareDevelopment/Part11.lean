/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDevelopedWinding.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment.Part10


namespace StatMech.FrontierD

noncomputable section

theorem fkRectSquareDeckTranslation_det
    (R : FKRectTorus) (u v : Int × Int) :
    (fkRectSquareDeckTranslation R u).1 *
          (fkRectSquareDeckTranslation R v).2 -
        (fkRectSquareDeckTranslation R u).2 *
          (fkRectSquareDeckTranslation R v).1 =
      -(R.width : Int) * R.height *
        (u.1 * v.2 - u.2 * v.1) := by
  have hhNat : 2 * (R.height / 2) = R.height :=
    Nat.two_mul_div_two_of_even R.height_even
  have hh : (2 : Int) * (R.height / 2 : Nat) = R.height := by
    exact_mod_cast hhNat
  simp only [fkRectSquareDeckTranslation, Prod.fst, Prod.snd]
  linear_combination
    -(R.width : Int) * u.1 * v.2 * hh +
      (R.width : Int) * u.2 * v.1 * hh


theorem fkRectWindingIndependent_squareDeck_iff
    (R : FKRectTorus) (u v : Int × Int) :
    FKRectWindingIndependent (fkRectSquareDeckTranslation R u)
        (fkRectSquareDeckTranslation R v) ↔
      FKRectWindingIndependent u v := by
  unfold FKRectWindingIndependent
  rw [fkRectSquareDeckTranslation_det]
  have hw : (R.width : Int) ≠ 0 := by
    exact_mod_cast (ne_of_gt R.width_pos)
  have hh : (R.height : Int) ≠ 0 := by
    exact_mod_cast (ne_of_gt R.height_pos)
  constructor
  · intro h hzero
    apply h
    rw [hzero]
    ring
  · intro h hscaled
    apply h
    have hcoefficient : -(R.width : Int) * R.height ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr hw) hh
    exact (mul_eq_zero.mp hscaled).resolve_left hcoefficient


theorem FKRectSquareWalkLift.closed_developedIndependent_iff
    (R : FKRectTorus)
    {G H : SimpleGraph R.Vertex} {x y : R.Vertex}
    {w : G.Walk x x} {z : H.Walk y y}
    {p q a b : Int × Int}
    (hw : FKRectSquareWalkLift R w p q)
    (hz : FKRectSquareWalkLift R z a b) :
    FKRectWindingIndependent
        (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p)
        (fkRectSquareDevelopPoint b - fkRectSquareDevelopPoint a) ↔
      FKRectWindingIndependent
        (fkRectWalkWinding R w) (fkRectWalkWinding R z) := by
  rw [hw.closed_develop_sub_eq_deck_winding R,
    hz.closed_develop_sub_eq_deck_winding R]
  exact fkRectWindingIndependent_squareDeck_iff R _ _


theorem fkRectOpenGraph_le_torusGraph
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectOpenGraph R omega ≤ fkRectTorusGraph R := by
  intro x y hxy
  obtain ⟨e, _, he⟩ := hxy
  exact ⟨e, he⟩


end
end StatMech.FrontierD
