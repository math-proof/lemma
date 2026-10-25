/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDevelopedWinding.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull.Part4
import Inductive.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment


namespace StatMech.FrontierD

noncomputable section

theorem fkRectWalk_exists_squareLift
    (R : FKRectTorus) {G : SimpleGraph R.Vertex}
    (hsub : G ≤ fkRectTorusGraph R) {x y : R.Vertex}
    (w : G.Walk x y) (p : Int × Int)
    (hp : fkRectLiftedVertex R p = x) :
    ∃ q : Int × Int, FKRectSquareWalkLift R w p q := by
  induction w generalizing p with
  | nil =>
      exact ⟨p, FKRectSquareWalkLift.nil p hp⟩
  | @cons x y z hxy w ih =>
      obtain ⟨q, hq, hdisp, haxis⟩ :=
        fkRectTorusGraph_adj_squareLift R (hsub hxy) p hp
      obtain ⟨r, htail⟩ := ih q hq
      exact ⟨r, FKRectSquareWalkLift.cons hp hq hdisp haxis htail⟩


theorem FKRectSquareWalkLift.end_project
    (R : FKRectTorus) {G : SimpleGraph R.Vertex}
    {x y : R.Vertex} {w : G.Walk x y} {p q : Int × Int}
    (h : FKRectSquareWalkLift R w p q) :
    fkRectLiftedVertex R q = y := by
  induction h with
  | nil p hp => exact hp
  | cons hp hq hdisp haxis tail ih => exact ih


theorem FKRectSquareWalkLift.sub_eq_developedDisplacement
    (R : FKRectTorus) {G : SimpleGraph R.Vertex}
    {x y : R.Vertex} {w : G.Walk x y} {p q : Int × Int}
    (h : FKRectSquareWalkLift R w p q) :
    q - p = fkRectWalkDevelopedDisplacement R w := by
  induction h with
  | nil p hp =>
      simp [fkRectWalkDevelopedDisplacement]
  | @cons x y z hxy w p q r hp hq hdisp haxis tail ih =>
      simp only [fkRectWalkDevelopedDisplacement]
      rw [← hdisp, ← ih]
      apply Prod.ext <;> simp <;> ring


theorem FKRectSquareWalkLift.closed_end_eq_period_winding
    (R : FKRectTorus) {G : SimpleGraph R.Vertex}
    {x : R.Vertex} {w : G.Walk x x} {p q : Int × Int}
    (h : FKRectSquareWalkLift R w p q) :
    q = (p.1 + (R.width : Int) * (fkRectWalkWinding R w).1,
      p.2 + (R.height : Int) * (fkRectWalkWinding R w).2) := by
  have hdisp := h.sub_eq_developedDisplacement R
  rw [fkRectClosedWalkDevelopedDisplacement_eq_period_winding] at hdisp
  apply Prod.ext
  · have hx := congrArg Prod.fst hdisp
    simp only [Prod.fst_sub, Prod.fst] at hx ⊢
    omega
  · have hy := congrArg Prod.snd hdisp
    simp only [Prod.snd_sub, Prod.snd] at hy ⊢
    omega


theorem FKRectSquareWalkLift.closed_develop_sub_eq_deck_winding
    (R : FKRectTorus) {G : SimpleGraph R.Vertex}
    {x : R.Vertex} {w : G.Walk x x} {p q : Int × Int}
    (h : FKRectSquareWalkLift R w p q) :
    fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p =
      fkRectSquareDeckTranslation R (fkRectWalkWinding R w) := by
  rw [h.closed_end_eq_period_winding R]
  exact fkRectSquareDevelopPoint_add_period R p
    (fkRectWalkWinding R w)


theorem fkRectVertexSquareClass_surjective (R : FKRectTorus) :
    Function.Surjective (fkRectVertexSquareClass R) := by
  intro q
  induction q using QuotientAddGroup.induction_on with
  | H z =>
      exact ⟨fkRectSquareRepresentativeVertex R z,
        fkRectVertexSquareClass_representative R z⟩


end
end StatMech.FrontierD
