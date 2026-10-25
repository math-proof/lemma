/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsing
import Def.StatisticalMechanics.Code.Sharpness.TildeBc.Part9
import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingFinite.Part10
import Def.StatisticalMechanics.Code.Sharpness.MeanfieldIsingFull
open MeasureTheory Real Set Filter Topology


namespace StatMech

namespace Sharpness

open StatMech.Lattice StatMech.Percolation StatMech.Ising


variable {d : ℕ}


theorem sct_infiniteField_meanfield_inequality_of_deriv_tendsto
    (d : ℕ) (beta h : ℝ)
    (hbdd : BddAbove (tildeBetaCIsingSet d))
    (habove : tildeBetaCIsing d < beta) (hh : 0 < h)
    (hderiv : Tendsto
      (fun n : ℕ => deriv
        (fun b => (sctOriginMag d b h (n + 1)) ^ 2) beta)
      atTop
      (nhds (deriv (fun b => (sctInfiniteFieldMag d b h) ^ 2) beta))) :
    (2 / beta) * (1 - (sctInfiniteFieldMag d beta h) ^ 2) ≤
      deriv (fun b => (sctInfiniteFieldMag d b h) ^ 2) beta := by
  have hzero : (0 : ℝ) ∈ tildeBetaCIsingSet d := by
    refine ⟨le_rfl, {origin d}, by simp, ?_⟩
    simp [phiIsing]
  have htc0 : 0 ≤ tildeBetaCIsing d := by
    unfold tildeBetaCIsing
    exact le_csSup hbdd hzero
  have hbeta : 0 < beta := lt_of_le_of_lt htc0 habove
  have hphi : ∀ S : Finset (Site d), origin d ∈ S →
      1 ≤ phiIsing d beta S :=
    si4_phiIsing_ge_one_above_tildeBc d beta hbeta.le hbdd habove
  let un : ℕ → ℝ := fun n => (sctOriginMag d beta h (n + 1)) ^ 2
  let un' : ℕ → ℝ := fun n =>
    deriv (fun b => (sctOriginMag d b h (n + 1)) ^ 2) beta
  let cn : ℕ → ℝ := fun n => sctLatticeC d beta h (n + 1)
  let epsn : ℕ → ℝ := fun n =>
    sctBoundaryCovarianceError d beta h (n + 1)
  have hmag := sctOriginMag_tendsto_iSup d beta h hbeta.le hh.le
  have hun : Tendsto un atTop
      (nhds ((sctInfiniteFieldMag d beta h) ^ 2)) := by
    exact (hmag.comp (tendsto_add_atTop_nat 1)).pow 2
  have hcn : Tendsto cn atTop (nhds 1) := by
    exact (sctLatticeC_tendsto_one d beta h hbeta hh).comp
      (tendsto_add_atTop_nat 1)
  have heps : Tendsto epsn atTop (nhds 0) := by
    exact (sctBoundaryCovarianceError_tendsto_zero d beta h hbeta hh).comp
      (tendsto_add_atTop_nat 1)
  apply si4_mfd_limit_passage beta 1 hbeta (le_refl 1)
    ((sctInfiniteFieldMag d beta h) ^ 2)
    (deriv (fun b => (sctInfiniteFieldMag d b h) ^ 2) beta)
    un un' cn epsn hun hderiv hcn heps
  · intro n
    exact sctLatticeC_nonneg beta h hbeta hh
  · intro n
    have hm0 : 0 ≤ sctOriginMag d beta h (n + 1) :=
      (sctOriginMag_pos d beta h hbeta hh (n + 1)).le
    have hm1 : sctOriginMag d beta h (n + 1) ≤ 1 :=
      sctOriginMag_le_one d beta h (n + 1)
    dsimp [un]
    nlinarith
  · intro n
    exact sct_finite_meanfield_inequality_concrete beta h 1
      (Nat.succ_le_succ (Nat.zero_le n)) hbeta hh hphi

end Sharpness
end StatMech
