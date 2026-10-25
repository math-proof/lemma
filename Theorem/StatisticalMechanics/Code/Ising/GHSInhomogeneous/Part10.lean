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
import Def.StatisticalMechanics.Code.Ising.GHSInhomogeneous.Part9
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option maxHeartbeats 2400000


namespace StatMech.Ising

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem ghsiUrsell3_nonpos (K : Sym2 V → ℝ) (hf : V → ℝ)
    (hK : ∀ e, 0 ≤ K e) (hhf : ∀ x, 0 ≤ hf x)
    (o x y : V) (hox : o ≠ x) :
    ghsiUrsell3 G K hf o x y ≤ 0 := by
  exact ghsi_ursell_nonpos G K hf hK hhf o x y hox

theorem ghsi_expJ_sum {I : Type*} (K : Sym2 V → ℝ) (hf : V → ℝ)
    (S : Finset I) (f : I → ConfigSpace V → ℝ) :
    expJ G.edgeFinset K hf (fun cfg => ∑ i ∈ S, f i cfg) =
      ∑ i ∈ S, expJ G.edgeFinset K hf (f i) := by
  unfold expJ
  change (∑ cfg : ConfigSpace V,
      (∑ i ∈ S, f i cfg) * wJ G.edgeFinset K hf cfg) /
      ZJ G.edgeFinset K hf = _
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm, Finset.sum_div]

theorem ghsi_expJ_const_mul (K : Sym2 V → ℝ) (hf : V → ℝ)
    (c : ℝ) (f : ConfigSpace V → ℝ) :
    expJ G.edgeFinset K hf (fun cfg => c * f cfg) =
      c * expJ G.edgeFinset K hf f := by
  unfold expJ
  change (∑ s : ConfigSpace V, (c * f s) * wJ G.edgeFinset K hf s) /
      ZJ G.edgeFinset K hf = c *
        ((∑ s : ConfigSpace V, f s * wJ G.edgeFinset K hf s) /
          ZJ G.edgeFinset K hf)
  rw [show (∑ s : ConfigSpace V, (c * f s) * wJ G.edgeFinset K hf s) =
      c * ∑ s : ConfigSpace V, f s * wJ G.edgeFinset K hf s by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring]
  ring

theorem ghsi_expJ_dirSpin (K : Sym2 V → ℝ) (hf dir : V → ℝ) :
    expJ G.edgeFinset K hf (ghsiDirSpin dir) =
      ∑ x, dir x * expJ G.edgeFinset K hf (fun s => spin s x) := by
  unfold ghsiDirSpin
  rw [ghsi_expJ_sum G K hf Finset.univ]
  apply Finset.sum_congr rfl
  intro x _
  exact ghsi_expJ_const_mul G K hf (dir x) (fun s => spin s x)

theorem ghsi_expJ_mul_dirSpin (K : Sym2 V → ℝ) (hf dir : V → ℝ)
    (f : ConfigSpace V → ℝ) :
    expJ G.edgeFinset K hf (fun s => f s * ghsiDirSpin dir s) =
      ∑ x, dir x * expJ G.edgeFinset K hf (fun s => f s * spin s x) := by
  have hfun : (fun s => f s * ghsiDirSpin dir s) =
      (fun s => ∑ x, dir x * (f s * spin s x)) := by
    funext s
    unfold ghsiDirSpin
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hfun, ghsi_expJ_sum G K hf Finset.univ]
  apply Finset.sum_congr rfl
  intro x _
  exact ghsi_expJ_const_mul G K hf (dir x) (fun s => f s * spin s x)

theorem ghsi_expJ_mul_dirSpin_sq (K : Sym2 V → ℝ) (hf dir : V → ℝ)
    (f : ConfigSpace V → ℝ) :
    expJ G.edgeFinset K hf
        (fun s => f s * ghsiDirSpin dir s * ghsiDirSpin dir s) =
      ∑ x, ∑ y, dir x * dir y *
        expJ G.edgeFinset K hf (fun s => f s * spin s x * spin s y) := by
  rw [ghsi_expJ_mul_dirSpin G K hf dir (fun s => f s * ghsiDirSpin dir s)]
  apply Finset.sum_congr rfl
  intro x _
  have hreorder : expJ G.edgeFinset K hf
      (fun s => f s * ghsiDirSpin dir s * spin s x) =
      expJ G.edgeFinset K hf
        (fun s => (f s * spin s x) * ghsiDirSpin dir s) := by
    congr 1
    funext s
    ring
  rw [hreorder, ghsi_expJ_mul_dirSpin G K hf dir (fun s => f s * spin s x)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring


end StatMech.Ising
