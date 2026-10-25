/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPreferenceInterface
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


theorem boolTransitionCount_parity (a : Bool) (xs : List Bool) :
    boolTransitionCount (a :: xs) % 2 =
      if a = (a :: xs).getLastD a then 0 else 1 := by
  induction xs generalizing a with
  | nil => simp [boolTransitionCount]
  | cons b xs ih =>
      have ihb := ih b
      rw [boolTransitionCount]
      rw [Nat.add_mod]
      simp only [List.getLastD_cons] at ihb ⊢
      generalize xs.getLastD b = z at ihb ⊢
      cases a <;> cases b <;> cases z <;>
        simp only [Bool.true_eq_false, Bool.false_eq_true, ite_false, ite_true,
          Nat.zero_mod, Nat.one_mod] at ihb ⊢ <;> omega


theorem boolTransitionCount_odd_of_ne_last (a : Bool) (xs : List Bool)
    (hne : a ≠ (a :: xs).getLastD a) :
    Odd (boolTransitionCount (a :: xs)) := by
  rw [Nat.odd_iff, boolTransitionCount_parity, if_neg hne]

end StatMech.FK.PeriodicPlanar
