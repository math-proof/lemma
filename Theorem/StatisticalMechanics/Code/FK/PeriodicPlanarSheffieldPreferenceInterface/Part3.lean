/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPreferenceInterface.Part2
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


theorem finBoolTransitionCount_parity {n : Nat}
    (f : Fin (n + 1) → Bool) :
    finBoolTransitionCount f % 2 =
      if f 0 = f (Fin.last n) then 0 else 1 := by
  induction n with
  | zero => simp [finBoolTransitionCount]
  | succ n ih =>
      unfold finBoolTransitionCount
      rw [Fin.sum_univ_succ, Nat.add_mod]
      simp only [← Fin.succ_castSucc]
      have hlast : (Fin.last n).succ = Fin.last (n + 1) := by
        apply Fin.ext
        rfl
      have iht := ih (fun i => f i.succ)
      unfold finBoolTransitionCount at iht
      dsimp only at iht
      have iht' : (∑ i : Fin n,
          if f i.castSucc.succ = f i.succ.succ then 0 else 1) % 2 =
          (if f 1 = f (Fin.last n).succ then 0 else 1) := by
        convert iht using 1
      calc
        _ = ((if f 0 = f 1 then 0 else 1) % 2 +
            (if f 1 = f (Fin.last n).succ then 0 else 1)) % 2 := by
          congr 2
        _ = _ := by
          rw [hlast]
          generalize f 0 = a
          generalize f 1 = b
          generalize f (Fin.last (n + 1)) = z
          cases a <;> cases b <;> cases z <;> simp

theorem finBoolTransitionCount_odd {n : Nat}
    (f : Fin (n + 1) → Bool) (hne : f 0 ≠ f (Fin.last n)) :
    Odd (finBoolTransitionCount f) := by
  rw [Nat.odd_iff, finBoolTransitionCount_parity, if_neg hne]


end StatMech.FK.PeriodicPlanar
