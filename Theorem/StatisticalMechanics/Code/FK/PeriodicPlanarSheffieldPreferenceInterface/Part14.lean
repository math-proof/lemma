/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPreferenceInterface.Part13
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


theorem walk_exists_last_mem_adj_notMem
    {W : Type*} {G : SimpleGraph W} (Y : Set W) {l r : W}
    (p : G.Walk l r) (hl : l ∈ Y) (hr : r ∉ Y) :
    ∃ x y : W, x ∈ p.support ∧ y ∈ p.support ∧
      G.Adj x y ∧ x ∈ Y ∧ y ∉ Y := by
  induction p with
  | nil => exact (hr hl).elim
  | @cons l m r hlm q ih =>
      by_cases hm : m ∈ Y
      · obtain ⟨x, y, hxq, hyq, hxy, hxY, hyY⟩ := ih hm hr
        exact ⟨x, y, by simp [hxq], by simp [hyq], hxy, hxY, hyY⟩
      · exact ⟨l, m, by simp, by simp, hlm, hl, hm⟩


theorem exists_preference_witness_of_boundary_walk
    (rectangle X Y : Set (Site 2))
    {l r : {x // x ∈ preferenceInnerBoundary rectangle X}}
    (p : (preferenceBoundaryGraph rectangle X).Walk l r)
    (hl : (l : Site 2) ∈ Y) (hr : (r : Site 2) ∉ Y) :
    ∃ x ∈ rectangle, x ∈ X ∧ x ∈ Y ∧
      (∃ x' ∈ rectangle, KingAdj x x' ∧ x' ∉ X) ∧
      (∃ x'' ∈ rectangle, KingAdj x x'' ∧ x'' ∉ Y) := by
  let Yb : Set {x // x ∈ preferenceInnerBoundary rectangle X} :=
    {x | (x : Site 2) ∈ Y}
  obtain ⟨x, y, _hxp, _hyp, hxy, hxY, hyY⟩ :=
    walk_exists_last_mem_adj_notMem Yb p hl hr
  obtain ⟨hxRect, hxX, x', hx'Rect, hxx', hx'X⟩ := x.2
  exact ⟨x, hxRect, hxX, hxY, ⟨x', hx'Rect, hxx', hx'X⟩,
    ⟨y, y.2.1, hxy, hyY⟩⟩

theorem exists_preference_witness_of_grid_boundary {n m : Nat}
    (color : PreferenceGridVertex n m → Bool) (hn : 0 < n)
    (hbottom : ∀ i : Fin (n + 1), color (i, 0) = true)
    (htop : ∀ i : Fin (n + 1), color (i, Fin.last m) = false)
    (Y : Set (Site 2))
    (hYleft : ∀ x : {x // x ∈ preferenceGridBoundary color},
      x.val.1.val = 0 →
        (preferenceGridBoundaryToSite color x : Site 2) ∈ Y)
    (hYright : ∀ x : {x // x ∈ preferenceGridBoundary color},
      x.val.1.val = n →
        (preferenceGridBoundaryToSite color x : Site 2) ∉ Y) :
    ∃ x ∈ preferenceGridRectangle n m,
      x ∈ preferenceGridTrueSet color ∧ x ∈ Y ∧
      (∃ x' ∈ preferenceGridRectangle n m, KingAdj x x' ∧
        x' ∉ preferenceGridTrueSet color) ∧
      (∃ x'' ∈ preferenceGridRectangle n m, KingAdj x x'' ∧ x'' ∉ Y) := by
  have hreach := preferenceInterface_left_reachable_right color hn true false
    hbottom htop (by decide)
  have hbottomZero := preferenceInterface_bottom_degree_zero color true hbottom
  have htopZero := preferenceInterface_top_degree_zero color false htop
  have hflag := preferenceFlagCrossing_of_reachable
    color hbottomZero htopZero hreach
  obtain ⟨leftPoint, rightPoint, hleft, hright, hgridReach⟩ :=
    preferenceGridBoundary_reachable_left_right_of_flagCrossing color hflag
  have hsiteReach := hgridReach.map (preferenceGridBoundaryGraphHom color)
  obtain ⟨p⟩ := hsiteReach
  exact exists_preference_witness_of_boundary_walk
    (preferenceGridRectangle n m) (preferenceGridTrueSet color) Y p
    (hYleft leftPoint hleft) (hYright rightPoint hright)

end StatMech.FK.PeriodicPlanar
