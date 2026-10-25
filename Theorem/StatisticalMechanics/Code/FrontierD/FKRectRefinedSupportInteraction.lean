/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedSupportInteraction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedInteractionCore.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedIntersection.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDisjointWinding.Part4
import Instance.StatisticalMechanics.Code.FrontierD.FKRectRefinedSupportInteraction
open Finset


namespace StatMech.FrontierD

open IntegralSquareTorusCycle

noncomputable section

variable {L : Nat} [Fact (8 < L)]

theorem fkRectRefinedRawInteraction_eq_zero_of_endpointDisjoint
    (v w : List (StatMech.Onsager.ons_Dart L))
    (hdisj : ∀ p, FKRectDartListUsesPoint v p →
      ¬ FKRectDartListUsesPoint w p) :
    fkRectRefinedRawInteraction v w = 0 := by
  classical
  unfold fkRectRefinedRawInteraction
  apply Finset.sum_eq_zero
  intro p hp
  by_cases hv :
      (v.map (fun d => dartHorizontal d p)).sum = 0 ∧
        (v.map (fun d => dartVertical d p)).sum = 0
  · rw [hv.1, hv.2]
    ring
  · have hwest :
        (w.map (fun d => dartHorizontal d (p.1 - 1, p.2))).sum = 0 := by
      by_contra hne
      have hvUses : FKRectDartListUsesPoint v p := by
        rcases not_and_or.mp hv with hh | hh
        · exact FKRectDartListUsesPoint.of_horizontal_ne_zero hh
        · exact FKRectDartListUsesPoint.of_vertical_ne_zero hh
      have hwUses := FKRectDartListUsesPoint.of_horizontal_ne_zero_east
        (l := w) hne
      apply hdisj p hvUses
      simpa using hwUses
    have hsouth :
        (w.map (fun d => dartVertical d (p.1, p.2 - 1))).sum = 0 := by
      by_contra hne
      have hvUses : FKRectDartListUsesPoint v p := by
        rcases not_and_or.mp hv with hh | hh
        · exact FKRectDartListUsesPoint.of_horizontal_ne_zero hh
        · exact FKRectDartListUsesPoint.of_vertical_ne_zero hh
      have hwUses := FKRectDartListUsesPoint.of_vertical_ne_zero_north
        (l := w) hne
      apply hdisj p hvUses
      simpa using hwUses
    rw [hwest, hsouth]
    ring

end

theorem fkRectIntCast_four_mul_add_ne_four_mul
    {L : Nat} [NeZero L] (hL : (4 : Int) ∣ (L : Int))
    (x a k : Int) (hk : ¬ (4 : Int) ∣ k) :
    ((4 * x + k : Int) : ZMod L) ≠ ((4 * a : Int) : ZMod L) := by
  intro h
  have hd : (L : Int) ∣ (4 * a) - (4 * x + k) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ L).mp h
  obtain ⟨m, hm⟩ := hd
  obtain ⟨n, hn⟩ := hL
  apply hk
  refine ⟨a - x - n * m, ?_⟩
  rw [hn] at hm
  linarith

theorem fkRectPointMass_west_normalized
    {L : Nat} [Fact (2 < L)]
    (a p : ZMod L × ZMod L) :
    pointMass a (-1 + p.1, p.2) =
      pointMass (a.1 + 1, a.2) p := by
  convert pointMass_west a p using 1 <;> ring

theorem fkRectPointMass_south_normalized
    {L : Nat} [Fact (2 < L)]
    (a p : ZMod L × ZMod L) :
    pointMass a (p.1, -1 + p.2) =
      pointMass (a.1, a.2 + 1) p := by
  convert pointMass_south a p using 1 <;> ring

@[simp] theorem fkRectIntegralSquareDartMod_dir
    (L : Nat) (d : FKRectIntegralSquareDart) :
    (fkRectIntegralSquareDartMod L d).2 = d.2 :=
  rfl


end StatMech.FrontierD
