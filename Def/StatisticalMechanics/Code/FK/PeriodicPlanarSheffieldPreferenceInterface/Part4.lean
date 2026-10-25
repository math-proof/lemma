/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
import Inductive.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPreferenceInterface
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


def preferenceTriangleVertex {n m : Nat} (t : PreferenceTriangle n m) :
    Fin 3 → PreferenceGridVertex n m
  | 0 => (t.col.castSucc, t.row.castSucc)
  | 1 => if t.upper then (t.col.succ, t.row.succ)
      else (t.col.succ, t.row.castSucc)
  | 2 => if t.upper then (t.col.castSucc, t.row.succ)
      else (t.col.succ, t.row.succ)

def preferenceTriangleNext : Fin 3 → Fin 3
  | 0 => 1
  | 1 => 2
  | 2 => 0

def preferenceTriangleSideActive {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (t : PreferenceTriangle n m) (k : Fin 3) : Prop :=
  color (preferenceTriangleVertex t k) ≠
    color (preferenceTriangleVertex t (preferenceTriangleNext k))


def preferenceTriangleOther {n m : Nat}
    (t : PreferenceTriangle n m) : Fin 3 → PreferenceInterfaceNode n m
  | 0 =>
      if t.upper then
        .triangle ⟨t.col, t.row, false⟩
      else if h : t.row.val = 0 then
        .bottom
      else
        .triangle ⟨t.col, ⟨t.row.val - 1, by omega⟩, true⟩
  | 1 =>
      if t.upper then
        if h : t.row.val + 1 = m then
          .top
        else
          .triangle ⟨t.col, ⟨t.row.val + 1, by omega⟩, false⟩
      else if h : t.col.val + 1 = n then
        .right
      else
        .triangle ⟨⟨t.col.val + 1, by omega⟩, t.row, true⟩
  | 2 =>
      if t.upper then
        if h : t.col.val = 0 then
          .left
        else
          .triangle ⟨⟨t.col.val - 1, by omega⟩, t.row, false⟩
      else
        .triangle ⟨t.col, t.row, true⟩

def preferenceInterfaceAdj {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (u v : PreferenceInterfaceNode n m) : Prop :=
  ∃ (t : PreferenceTriangle n m) (k : Fin 3),
    preferenceTriangleSideActive color t k ∧
      ((u = .triangle t ∧ v = preferenceTriangleOther t k) ∨
       (v = .triangle t ∧ u = preferenceTriangleOther t k))

end StatMech.FK.PeriodicPlanar
