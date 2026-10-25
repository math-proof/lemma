/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareCoverIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment.Part12
import Theorem.StatisticalMechanics.Code.FrontierD.IntegralSquareTorusIntersection.Part9
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareCoverIntersection.Part4
open scoped BigOperators


namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

@[simp] theorem fkRectIntegralSquareDartMod_site_eq_pointMod
    (L : Nat) (d : FKRectIntegralSquareDart) :
    (fkRectIntegralSquareDartMod L d).1 =
      fkRectIntegralSquarePointMod L d.1 :=
  rfl


theorem FKRectIntegralSquareDartPath.pointMass_telescope
    {p q : Int × Int} {l : List FKRectIntegralSquareDart}
    (h : FKRectIntegralSquareDartPath p q l) (L : Nat)
    (z : ZMod L × ZMod L) :
    ((l.map (fkRectIntegralSquareDartMod L)).map
        (fun d => IntegralSquareTorusCycle.pointMass d.1 z)).sum -
      ((l.map (fkRectIntegralSquareDartMod L)).map
        (fun d => IntegralSquareTorusCycle.pointMass
          (ons_dirStep L d.2 d.1) z)).sum =
    IntegralSquareTorusCycle.pointMass
        (fkRectIntegralSquarePointMod L p) z -
      IntegralSquareTorusCycle.pointMass
        (fkRectIntegralSquarePointMod L q) z := by
  induction h with
  | nil p => simp
  | @cons d q r l hend tail ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [fkRectIntegralSquareDartMod_end, hend]
      change IntegralSquareTorusCycle.pointMass
            (fkRectIntegralSquarePointMod L d.1) z +
            ((l.map (fkRectIntegralSquareDartMod L)).map
              (fun d => IntegralSquareTorusCycle.pointMass d.1 z)).sum -
          (IntegralSquareTorusCycle.pointMass
              (fkRectIntegralSquarePointMod L q) z +
            ((l.map (fkRectIntegralSquareDartMod L)).map
              (fun d => IntegralSquareTorusCycle.pointMass
                (ons_dirStep L d.2 d.1) z)).sum) = _
      linear_combination ih


theorem FKRectIntegralSquareDartPath.dartListBalanced_of_pointMod_eq
    {p q : Int × Int} {l : List FKRectIntegralSquareDart}
    (h : FKRectIntegralSquareDartPath p q l) (L : Nat)
    (hend : fkRectIntegralSquarePointMod L p =
      fkRectIntegralSquarePointMod L q) :
    IntegralSquareTorusCycle.DartListBalanced
      (l.map (fkRectIntegralSquareDartMod L)) := by
  intro z
  have htelescope := h.pointMass_telescope L z
  rw [hend, sub_self] at htelescope
  exact sub_eq_zero.mp htelescope

section Wrap

variable {L : Nat} [Fact (2 < L)]

theorem fkRectIntegralSquareDart_displacement_x
    (d : FKRectIntegralSquareDart) :
    (fkRectIntegralSquareDartEnd d).1 - d.1.1 =
      (((fkRectIntegralSquarePointMod L
          (fkRectIntegralSquareDartEnd d)).1.val : Nat) : Int) -
        (((fkRectIntegralSquarePointMod L d.1).1.val : Nat) : Int) +
        (L : Int) * ons_xWrapSign (fkRectIntegralSquareDartMod L d) := by
  have h := ons_dirExponentX_eq_val_diff_add_wrap
    (fkRectIntegralSquareDartMod L d)
  rw [fkRectIntegralSquareDartMod_end] at h
  calc
    (fkRectIntegralSquareDartEnd d).1 - d.1.1 =
        ons_dirExponentX d.2 := by
          simp [fkRectIntegralSquareDartEnd]
    _ = _ := h

theorem fkRectIntegralSquareDart_displacement_y
    (d : FKRectIntegralSquareDart) :
    (fkRectIntegralSquareDartEnd d).2 - d.1.2 =
      (((fkRectIntegralSquarePointMod L
          (fkRectIntegralSquareDartEnd d)).2.val : Nat) : Int) -
        (((fkRectIntegralSquarePointMod L d.1).2.val : Nat) : Int) +
        (L : Int) * ons_yWrapSign (fkRectIntegralSquareDartMod L d) := by
  have h := ons_dirExponentY_eq_val_diff_add_wrap
    (fkRectIntegralSquareDartMod L d)
  rw [fkRectIntegralSquareDartMod_end] at h
  calc
    (fkRectIntegralSquareDartEnd d).2 - d.1.2 =
        ons_dirExponentY d.2 := by
          simp [fkRectIntegralSquareDartEnd]
    _ = _ := h


theorem FKRectIntegralSquareDartPath.displacement_x_eq_wrap
    {p q : Int × Int} {l : List FKRectIntegralSquareDart}
    (h : FKRectIntegralSquareDartPath p q l) :
    q.1 - p.1 =
      (((fkRectIntegralSquarePointMod L q).1.val : Nat) : Int) -
        (((fkRectIntegralSquarePointMod L p).1.val : Nat) : Int) +
        (L : Int) *
          ((l.map (fkRectIntegralSquareDartMod L)).map
            ons_xWrapSign).sum := by
  induction h with
  | nil p => simp
  | @cons d q r l hend tail ih =>
      have hd := fkRectIntegralSquareDart_displacement_x (L := L) d
      rw [hend] at hd
      simp only [List.map_cons, List.sum_cons]
      linear_combination hd + ih


theorem FKRectIntegralSquareDartPath.displacement_y_eq_wrap
    {p q : Int × Int} {l : List FKRectIntegralSquareDart}
    (h : FKRectIntegralSquareDartPath p q l) :
    q.2 - p.2 =
      (((fkRectIntegralSquarePointMod L q).2.val : Nat) : Int) -
        (((fkRectIntegralSquarePointMod L p).2.val : Nat) : Int) +
        (L : Int) *
          ((l.map (fkRectIntegralSquareDartMod L)).map
            ons_yWrapSign).sum := by
  induction h with
  | nil p => simp
  | @cons d q r l hend tail ih =>
      have hd := fkRectIntegralSquareDart_displacement_y (L := L) d
      rw [hend] at hd
      simp only [List.map_cons, List.sum_cons]
      linear_combination hd + ih

end Wrap
end
end StatMech.FrontierD
