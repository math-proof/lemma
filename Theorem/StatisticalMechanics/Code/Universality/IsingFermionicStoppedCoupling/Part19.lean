/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Def.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part23


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem globalReflectHitSplit_steps
    (R : Nat) {start : Int × Int} {level : Int}
    (split : IsingDiagonalWalkHitSplit start level) :
    (globalReflectHitSplit R split).steps = split.steps.map reflectIncrement := by
  unfold globalReflectHitSplit IsingDiagonalWalkHitSplit.steps
  exact List.map_append.symm

theorem globalReflectHitSplit_firstHit
    (R : Nat) {start : Int × Int} {level : Int}
    (split : IsingDiagonalWalkHitSplit start level) (hfirst : split.FirstHit) :
    (globalReflectHitSplit R split).FirstHit := by
  intro k hk heq
  have hk' : k < split.before.length := by simpa [globalReflectHitSplit] using hk
  have horig := hfirst k hk'
  have href :
      (isingDiagonalWalkEndpoint ((R : Int) - start.1, start.2)
        (((globalReflectHitSplit R split).before).take k)).1 =
      (R : Int) -
        (isingDiagonalWalkEndpoint start (split.before.take k)).1 := by
    rw [show ((globalReflectHitSplit R split).before).take k =
        (split.before.take k).map reflectIncrement by
      simp [globalReflectHitSplit, List.map_take]]
    unfold isingDiagonalWalkEndpoint
    rw [displacement_map_reflectIncrement]
    ring
  rw [heq] at href
  apply horig
  omega

theorem boxInt_reflectX
    (R : Nat) (p : IsingLeapfrogBox R) :
    isingLeapfrogBoxInt (isingLeapfrogBoxReflectX R p) =
      ((R : Int) - (isingLeapfrogBoxInt p).1, (isingLeapfrogBoxInt p).2) := by
  unfold isingLeapfrogBoxInt isingLeapfrogBoxReflectX
  dsimp
  apply Prod.ext
  · push_cast
    omega
  · rfl

end
end StatMech.Universality
