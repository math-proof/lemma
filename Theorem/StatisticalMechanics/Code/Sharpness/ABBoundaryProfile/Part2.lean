/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryProfile.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.ABMeanfieldGhost
import Theorem.StatisticalMechanics.Code.Sharpness.CToOneLattice.Part4
import Def.StatisticalMechanics.Code.Sharpness.ABBoundaryProfile.Part2
open Finset Set SimpleGraph


namespace StatMech

namespace Sharpness

open ConfigSpace RandomCurrent Lattice


theorem abbMag_differentiableAt_joint (d n : Nat) (beta h : Real) :
    DifferentiableAt Real (Function.uncurry (abbMag d n)) (beta, h) := by
  exact abfa_differentiableAt_prob_joint (sctBoxGraph d n)
    (abbCoupling d n)
    (connEvent (withGhost (sctBoxGraph d n)) Set.univ
      (some (sctBoxOrigin d n)) (abbTarget d n)) beta h


theorem abbMag_meanfield (d n : Nat) (beta h : Real)
    (hbeta : 0 <= beta) (hh : 0 <= h)
    (hphi : ∀ S : Finset (Option (sctBox d n)),
      some (sctBoxOrigin d n) ∈ S ->
      (mpiSurfaceEvent (withGhost (sctBoxGraph d n)) (abbTarget d n) S).Nonempty ->
        1 <= abbPhi d n beta h S) :
    1 - abbMag d n beta h <=
      beta * deriv (fun b => abbMag d n b h) beta := by
  have hJ : ∀ e ∈ (sctBoxGraph d n).edgeFinset,
      0 <= abbCoupling d n e := by
    intro e he
    simp [abbCoupling]
  have h := abmg_meanfield_target_finite (sctBoxGraph d n)
    (abbCoupling d n) (sctBoxOrigin d n) (abbTarget d n)
    beta h 1 hJ hbeta hh (by
      intro S hoS hocc
      exact hphi S hoS hocc)
  simpa [abbMag, abbPhi] using h


theorem abbMag_aizenmanBarsky_le_envelope
    (d n : Nat) (beta h J0 U : Real)
    (hrow : ∀ x, abcrIncidentCoupling (sctBoxGraph d n)
      (abbCoupling d n) x <= J0)
    (hbeta : 0 <= beta) (hh : 0 <= h) (hU : 0 <= U)
    (htarget : ∀ x : sctBox d n,
      probV (abfaParams (sctBoxGraph d n) (abbCoupling d n) beta h)
        (connEvent (withGhost (sctBoxGraph d n)) Set.univ
          (some x) (abbTarget d n)) <= U) :
    deriv (fun b => abbMag d n b h) beta <=
      J0 * U * deriv (fun t => abbMag d n beta t) h := by
  have hJ : ∀ e ∈ (sctBoxGraph d n).edgeFinset,
      0 <= abbCoupling d n e := by
    intro e he
    simp [abbCoupling]
  simpa [abbMag] using
    (abfa_aizenmanBarsky_target_le_envelope (sctBoxGraph d n)
      (abbCoupling d n) (sctBoxOrigin d n) (abbTarget d n)
      beta h J0 U (none_mem_abbTarget d n) hJ hrow hbeta hh hU htarget)

end Sharpness
end StatMech
