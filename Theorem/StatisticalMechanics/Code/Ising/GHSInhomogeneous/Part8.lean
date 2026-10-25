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
import Def.StatisticalMechanics.Code.Ising.GHSInhomogeneous.Part7
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option maxHeartbeats 2400000


namespace StatMech.Ising

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem ghsi_hasDerivAt_wJ_fieldLine (K : Sym2 V → ℝ)
    (hf dir : V → ℝ) (s : ConfigSpace V) (t : ℝ) :
    HasDerivAt (fun u => wJ G.edgeFinset K (ghsiFieldLine hf dir u) s)
      (wJ G.edgeFinset K (ghsiFieldLine hf dir t) s * ghsiDirSpin dir s) t := by
  unfold wJ ghsiFieldLine ghsiDirSpin
  have hfield : HasDerivAt
      (fun u => ∑ x : V, (hf x + u * dir x) * spin s x)
      (∑ x : V, dir x * spin s x) t := by
    have hfun : (fun u => ∑ x : V, (hf x + u * dir x) * spin s x) =
        ∑ x : V, (fun u => (hf x + u * dir x) * spin s x) := by
      rw [Finset.sum_fn]
    rw [hfun]
    apply HasDerivAt.sum
    intro x _
    convert (((hasDerivAt_const t (hf x)).add
      ((hasDerivAt_id t).mul_const (dir x))).mul_const (spin s x)) using 1 <;> ring
  have hexp := ((hasDerivAt_const t
    (∑ e ∈ G.edgeFinset, K e * bond s e)).add hfield).exp
  simpa only [Pi.add_apply, zero_add, mul_comm] using hexp

theorem ghsi_hasDerivAt_Z_fieldLine (K : Sym2 V → ℝ)
    (hf dir : V → ℝ) (t : ℝ) :
    HasDerivAt (fun u => ZJ G.edgeFinset K (ghsiFieldLine hf dir u))
      (∑ s : ConfigSpace V,
        wJ G.edgeFinset K (ghsiFieldLine hf dir t) s * ghsiDirSpin dir s) t := by
  unfold ZJ
  have hfun : (fun u => ∑ s : ConfigSpace V,
      wJ G.edgeFinset K (ghsiFieldLine hf dir u) s) =
      ∑ s : ConfigSpace V,
        (fun u => wJ G.edgeFinset K (ghsiFieldLine hf dir u) s) := by
    rw [Finset.sum_fn]
  rw [hfun]
  exact HasDerivAt.sum (fun s _ => ghsi_hasDerivAt_wJ_fieldLine G K hf dir s t)

theorem ghsi_hasDerivAt_num_fieldLine (K : Sym2 V → ℝ)
    (hf dir : V → ℝ) (f : ConfigSpace V → ℝ) (t : ℝ) :
    HasDerivAt (fun u => ∑ s : ConfigSpace V,
        f s * wJ G.edgeFinset K (ghsiFieldLine hf dir u) s)
      (∑ s : ConfigSpace V,
        f s * (wJ G.edgeFinset K (ghsiFieldLine hf dir t) s * ghsiDirSpin dir s)) t := by
  have hfun : (fun u => ∑ s : ConfigSpace V,
      f s * wJ G.edgeFinset K (ghsiFieldLine hf dir u) s) =
      ∑ s : ConfigSpace V,
        (fun u => f s * wJ G.edgeFinset K (ghsiFieldLine hf dir u) s) := by
    rw [Finset.sum_fn]
  rw [hfun]
  apply HasDerivAt.sum
  intro s _
  exact (ghsi_hasDerivAt_wJ_fieldLine G K hf dir s t).const_mul (f s)


theorem ghsi_hasDerivAt_expectation_fieldLine (K : Sym2 V → ℝ)
    (hf dir : V → ℝ) (f : ConfigSpace V → ℝ) (t : ℝ) :
    HasDerivAt (fun u => expJ G.edgeFinset K (ghsiFieldLine hf dir u) f)
      (expJ G.edgeFinset K (ghsiFieldLine hf dir t)
          (fun s => f s * ghsiDirSpin dir s) -
        expJ G.edgeFinset K (ghsiFieldLine hf dir t) f *
          expJ G.edgeFinset K (ghsiFieldLine hf dir t) (ghsiDirSpin dir)) t := by
  let hft := ghsiFieldLine hf dir t
  have hN := ghsi_hasDerivAt_num_fieldLine G K hf dir f t
  have hZ := ghsi_hasDerivAt_Z_fieldLine G K hf dir t
  have hZne : ZJ G.edgeFinset K hft ≠ 0 := (ZJ_pos _ _ _).ne'
  unfold expJ
  have hdiv := hN.div hZ hZne
  convert hdiv using 1
  · set Z := ZJ G.edgeFinset K hft
    set A := ∑ s : ConfigSpace V,
      f s * (wJ G.edgeFinset K hft s * ghsiDirSpin dir s)
    set B := ∑ s : ConfigSpace V, f s * wJ G.edgeFinset K hft s
    set C := ∑ s : ConfigSpace V, wJ G.edgeFinset K hft s * ghsiDirSpin dir s
    have hA : (∑ s : ConfigSpace V,
        f s * ghsiDirSpin dir s * wJ G.edgeFinset K hft s) = A := by
      change (∑ s : ConfigSpace V,
        f s * ghsiDirSpin dir s * wJ G.edgeFinset K hft s) =
        ∑ s : ConfigSpace V, f s * (wJ G.edgeFinset K hft s * ghsiDirSpin dir s)
      apply Finset.sum_congr rfl
      intro s _
      ring
    have hC : (∑ s : ConfigSpace V,
        ghsiDirSpin dir s * wJ G.edgeFinset K hft s) = C := by
      change (∑ s : ConfigSpace V,
        ghsiDirSpin dir s * wJ G.edgeFinset K hft s) =
        ∑ s : ConfigSpace V, wJ G.edgeFinset K hft s * ghsiDirSpin dir s
      apply Finset.sum_congr rfl
      intro s _
      ring
    rw [hA, hC]
    change A / Z - B / Z * (C / Z) = (A * Z - B * C) / Z ^ 2
    field_simp


end StatMech.Ising
