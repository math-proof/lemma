/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.GHSLebowitz.Part11
import Theorem.StatisticalMechanics.Code.Ising.GHSInhomVertexPartition.Part3
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeRelabel
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeSum
import Theorem.StatisticalMechanics.Code.Sharpness.GHSConcavity
import Def.StatisticalMechanics.Code.Ising.GHSInhomogeneous.Part10
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option maxHeartbeats 2400000


namespace StatMech.Ising

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem ghsi_directionalCovariance_eq_sum_covariance
    (K : Sym2 V → ℝ) (hf dir : V → ℝ) (o : V) :
    ghsiDirectionalCovariance G K hf dir (fun s => spin s o) =
      ∑ x, dir x * ghsiCovariance G K hf o x := by
  unfold ghsiDirectionalCovariance ghsiCovariance
  rw [ghsi_expJ_mul_dirSpin G K hf dir (fun s => spin s o),
    ghsi_expJ_dirSpin G K hf dir, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring


theorem ghsi_hasDerivAt_covariance_fieldLine
    (K : Sym2 V → ℝ) (hf dir : V → ℝ) (o x : V) (t : ℝ) :
    HasDerivAt
      (fun u => ghsiCovariance G K (ghsiFieldLine hf dir u) o x)
      (∑ y, dir y * ghsiUrsell3 G K (ghsiFieldLine hf dir t) o x y) t := by
  unfold ghsiCovariance
  have h := (ghsi_hasDerivAt_expectation_fieldLine G K hf dir
      (fun s => spin s o * spin s x) t).sub
    ((ghsi_hasDerivAt_expectation_fieldLine G K hf dir (fun s => spin s o) t).mul
      (ghsi_hasDerivAt_expectation_fieldLine G K hf dir (fun s => spin s x) t))
  convert h using 1
  rw [ghsi_expJ_mul_dirSpin G K (ghsiFieldLine hf dir t) dir
      (fun s => spin s o * spin s x),
    ghsi_expJ_dirSpin G K (ghsiFieldLine hf dir t) dir,
    ghsi_expJ_mul_dirSpin G K (ghsiFieldLine hf dir t) dir (fun s => spin s o),
    ghsi_expJ_mul_dirSpin G K (ghsiFieldLine hf dir t) dir (fun s => spin s x)]
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  unfold ghsiUrsell3
  have hassoc : expJ G.edgeFinset K (ghsiFieldLine hf dir t)
      (fun s => spin s o * spin s x * spin s y) =
      expJ G.edgeFinset K (ghsiFieldLine hf dir t)
        (fun s => spin s o * (spin s x * spin s y)) := by
    congr 1
    funext s
    ring
  rw [hassoc]
  ring

theorem ghsi_hasDerivAt_directionalCovariance_ursellSum
    (K : Sym2 V → ℝ) (hf dir : V → ℝ) (o : V) (t : ℝ) :
    HasDerivAt
      (fun u => ghsiDirectionalCovariance G K (ghsiFieldLine hf dir u) dir
        (fun s => spin s o))
      (∑ x, ∑ y, dir x * dir y *
        ghsiUrsell3 G K (ghsiFieldLine hf dir t) o x y) t := by
  have hfun : (fun u => ghsiDirectionalCovariance G K
      (ghsiFieldLine hf dir u) dir (fun s => spin s o)) =
      (fun u => ∑ x, dir x *
        ghsiCovariance G K (ghsiFieldLine hf dir u) o x) := by
    funext u
    exact ghsi_directionalCovariance_eq_sum_covariance G K
      (ghsiFieldLine hf dir u) dir o
  rw [hfun]
  have hsum : HasDerivAt
      (fun u => ∑ x, dir x *
        ghsiCovariance G K (ghsiFieldLine hf dir u) o x)
      (∑ x, dir x *
        (∑ y, dir y * ghsiUrsell3 G K (ghsiFieldLine hf dir t) o x y)) t := by
    have hsumfun : (fun u => ∑ x, dir x *
        ghsiCovariance G K (ghsiFieldLine hf dir u) o x) =
        ∑ x : V, (fun u => dir x *
          ghsiCovariance G K (ghsiFieldLine hf dir u) o x) := by
      rw [Finset.sum_fn]
    rw [hsumfun]
    apply HasDerivAt.sum
    intro x _
    exact (ghsi_hasDerivAt_covariance_fieldLine G K hf dir o x t).const_mul (dir x)
  convert hsum using 1
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring


theorem ghsi_directionalCovariance_derivValue_eq_ursellSum
    (K : Sym2 V → ℝ) (hf dir : V → ℝ) (o : V) :
    (expJ G.edgeFinset K hf
          (fun s => spin s o * ghsiDirSpin dir s * ghsiDirSpin dir s) -
        expJ G.edgeFinset K hf (fun s => spin s o * ghsiDirSpin dir s) *
          expJ G.edgeFinset K hf (ghsiDirSpin dir) -
        (expJ G.edgeFinset K hf (fun s => spin s o * ghsiDirSpin dir s) -
          expJ G.edgeFinset K hf (fun s => spin s o) *
            expJ G.edgeFinset K hf (ghsiDirSpin dir)) *
          expJ G.edgeFinset K hf (ghsiDirSpin dir) -
        expJ G.edgeFinset K hf (fun s => spin s o) *
          (expJ G.edgeFinset K hf
              (fun s => ghsiDirSpin dir s * ghsiDirSpin dir s) -
            expJ G.edgeFinset K hf (ghsiDirSpin dir) *
              expJ G.edgeFinset K hf (ghsiDirSpin dir))) =
      ∑ x, ∑ y, dir x * dir y * ghsiUrsell3 G K hf o x y := by
  have hraw := ghsi_hasDerivAt_directionalCovariance G K hf dir
    (fun s => spin s o) 0
  have hsum := ghsi_hasDerivAt_directionalCovariance_ursellSum G K hf dir o 0
  have hline : ghsiFieldLine hf dir 0 = hf := by
    funext x
    simp [ghsiFieldLine]
  rw [hline] at hraw hsum
  exact hraw.unique hsum


theorem ghsi_magnetization_fieldLine_concaveOn
    (K : Sym2 V → ℝ) (hf dir : V → ℝ)
    (hK : ∀ e, 0 ≤ K e) (hhf : ∀ x, 0 ≤ hf x)
    (hdir : ∀ x, 0 ≤ dir x) (o : V) (hdiro : dir o = 0) :
    ConcaveOn ℝ (Ici 0)
      (fun t => expJ G.edgeFinset K (ghsiFieldLine hf dir t)
        (fun s => spin s o)) := by
  let phi : ℝ → ℝ := fun t => expJ G.edgeFinset K (ghsiFieldLine hf dir t)
    (fun s => spin s o)
  have hphi (t : ℝ) : HasDerivAt phi
      (ghsiDirectionalCovariance G K (ghsiFieldLine hf dir t) dir
        (fun s => spin s o)) t := by
    exact ghsi_hasDerivAt_expectation_fieldLine G K hf dir (fun s => spin s o) t
  have hderiv : deriv phi = fun t =>
      ghsiDirectionalCovariance G K (ghsiFieldLine hf dir t) dir
        (fun s => spin s o) := by
    funext t
    exact (hphi t).deriv
  apply Sharpness.shg_concaveOn_of_deriv2_nonpos
  · intro t _
    exact (hphi t).continuousAt.continuousWithinAt
  · intro t _
    exact (hphi t).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro t _
    rw [hderiv]
    have hd := ghsi_hasDerivAt_directionalCovariance_ursellSum G K hf dir o t
    exact hd.differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro t ht
    change deriv (deriv phi) t ≤ 0
    rw [hderiv]
    rw [(ghsi_hasDerivAt_directionalCovariance_ursellSum G K hf dir o t).deriv]
    apply Finset.sum_nonpos
    intro x _
    apply Finset.sum_nonpos
    intro y _
    by_cases hxo : x = o
    · subst x
      rw [hdiro]
      simp
    · have hfield : ∀ z, 0 ≤ ghsiFieldLine hf dir t z := by
        intro z
        unfold ghsiFieldLine
        exact add_nonneg (hhf z) (mul_nonneg ht.le (hdir z))
      exact mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (hdir x) (hdir y))
        (ghsiUrsell3_nonpos G K (ghsiFieldLine hf dir t) hK hfield o x y
          (Ne.symm hxo))


theorem ghsi_directionalCovariance_le_secant
    (K : Sym2 V → ℝ) (hf dir : V → ℝ)
    (hK : ∀ e, 0 ≤ K e) (hhf : ∀ x, 0 ≤ hf x)
    (hdir : ∀ x, 0 ≤ dir x) (o : V) (hdiro : dir o = 0)
    {b : ℝ} (hb : 0 < b) :
    ghsiDirectionalCovariance G K (ghsiFieldLine hf dir b) dir
        (fun s => spin s o) ≤
      (expJ G.edgeFinset K (ghsiFieldLine hf dir b) (fun s => spin s o) -
        expJ G.edgeFinset K (ghsiFieldLine hf dir 0) (fun s => spin s o)) / b := by
  let phi : ℝ → ℝ := fun t => expJ G.edgeFinset K (ghsiFieldLine hf dir t)
    (fun s => spin s o)
  have hconc := ghsi_magnetization_fieldLine_concaveOn G K hf dir hK hhf hdir o hdiro
  have hslope := Sharpness.shg_concaveOn_deriv_le_slope phi hconc
    (mem_Ici.mpr le_rfl) (mem_Ici.mpr hb.le) hb
    (ghsi_hasDerivAt_expectation_fieldLine G K hf dir
      (fun s => spin s o) b).differentiableAt
  rw [(ghsi_hasDerivAt_expectation_fieldLine G K hf dir
    (fun s => spin s o) b).deriv] at hslope
  simpa [phi, ghsiDirectionalCovariance, sub_zero] using hslope

end StatMech.Ising
