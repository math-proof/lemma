/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnClassification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialLoopTurnGeometry.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectMedialLoopTurnClassification.Part3
open Equiv Finset


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

open FKMedialTurningFiber

noncomputable section

variable {T : EvenTorus}

@[simp] theorem fkRectBlackOrbitPrefix_zero
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T) :
    fkRectBlackOrbitPrefix pairing d 0 = 0 := by
  simp [fkRectBlackOrbitPrefix]

theorem fkRectBlackOrbitPrefix_succ
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T)
    (n : Nat) :
    fkRectBlackOrbitPrefix pairing d (n + 1) =
      fkRectBlackOrbitPrefix pairing d n +
        stepOf (fkMedialStrandDirection pairing
          ((fkMedialBlackBoundaryPerm pairing)^[n] d).1) := by
  rw [fkRectBlackOrbitPrefix, fkRectBlackOrbitPrefix,
    Finset.sum_range_succ]

theorem fkRectBlackBoundaryPointAfter_eq_prefix
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialBlackDart R.medialTorus) (n : Nat) :
    fkRectBlackBoundaryPointAfter R pairing d n =
      fkRectBlackBoundaryPointAfter R pairing d 0 +
        2 • fkRectBlackOrbitPrefix pairing d n := by
  induction n with
  | zero => simp
  | succ n ih =>
      let e := fkMedialStrandDirection pairing
        ((fkMedialBlackBoundaryPerm pairing)^[n] d).1
      calc
        fkRectBlackBoundaryPointAfter R pairing d (Nat.succ n) =
            fkRectBlackBoundaryPointAfter R pairing d n +
              2 • stepOf e := by
          rw [show Nat.succ n = n + 1 by omega,
            fkRectBlackBoundaryPointAfter_succ,
            ons_stepOf_eq_exponents]
          apply Prod.ext <;> simp [e]
        _ = (fkRectBlackBoundaryPointAfter R pairing d 0 +
              2 • fkRectBlackOrbitPrefix pairing d n) +
              2 • stepOf e := by rw [ih]
        _ = fkRectBlackBoundaryPointAfter R pairing d 0 +
              2 • fkRectBlackOrbitPrefix pairing d (Nat.succ n) := by
          rw [show Nat.succ n = n + 1 by omega,
            fkRectBlackOrbitPrefix_succ, nsmul_add]
          abel

theorem fkRectBlackOrbitPrefix_eq_pos
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T)
    [NeZero (fkRectBlackOrbitList pairing d).length]
    (i : Fin (fkRectBlackOrbitList pairing d).length) :
    fkRectBlackOrbitPrefix pairing d i.val =
      pos (fkRectBlackOrbitDirection pairing d) i := by
  unfold fkRectBlackOrbitPrefix pos
  apply Finset.sum_bij (fun k hk =>
    ⟨k, (Finset.mem_range.mp hk).trans i.isLt⟩)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
    exact Finset.mem_range.mp hk
  · intro a ha b hb hab
    exact congrArg Fin.val hab
  · intro j hj
    have hji : j.val < i.val := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
        using hj
    refine ⟨j.val, Finset.mem_range.mpr hji, ?_⟩
    exact Fin.ext rfl
  · intro k hk
    simp only [fkRectBlackOrbitDirection, fkRectBlackOrbitList_get]

theorem fkRectBlackOrbitPrefix_length_eq_displacement
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T) :
    fkRectBlackOrbitPrefix pairing d
        (fkRectBlackOrbitList pairing d).length =
      ons_pathDisplacement
        (List.ofFn (fkRectBlackOrbitDirection pairing d)) := by
  rw [ons_pathDisplacement_ofFn, fkRectBlackOrbitPrefix]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  simp only [fkRectBlackOrbitDirection, fkRectBlackOrbitList_get]

theorem fkRectBlackBoundaryPerm_pow_length_apply
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T) :
    (fkMedialBlackBoundaryPerm pairing)^[
        (fkRectBlackOrbitList pairing d).length] d = d := by
  let p := fkMedialBlackBoundaryPerm pairing
  have hd : p d ≠ d := fkMedialBlackBoundaryPerm_apply_ne pairing d
  change (p ^ (p.toList d).length) d = d
  rw [Equiv.Perm.length_toList,
    ← (Equiv.Perm.isCycle_cycleOf p hd).orderOf,
    ← Equiv.Perm.cycleOf_pow_apply_self,
    pow_orderOf_eq_one, Equiv.Perm.one_apply]

@[simp] theorem fkRectBlackBoundaryPointAfter_zero
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialBlackDart R.medialTorus) :
    fkRectBlackBoundaryPointAfter R pairing d 0 =
      fkRectBlackDartShiftedPoint R (0, 0) d := by
  simp [fkRectBlackBoundaryPointAfter, fkRectBlackDartShiftedPoint,
    fkRectRefinedBoundaryCenterAfter, fkRectSquareDeckTranslation]

end
end StatMech.FrontierD
