/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.DifferentialAnalysis.code.TestFunctions
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.TestFunctions
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Def.v1.Atlas.DifferentialAnalysis.code.SobolevEmbedding
open scoped ZeroAtInfty
open MeasureTheory Filter Topology


noncomputable section

namespace SobolevEmbedding

set_option synthInstance.maxHeartbeats 80000 in
/-- For `u ∈ H^m` and a coordinate direction `j`, the partial derivative
`∂_j u` has all iterated derivatives up to order `m-1` in `L^2`. This is the
key technical lemma used to define `SobolevSpace.partialDeriv`. -/
theorem partialDeriv_iteratedFDeriv_memLp {n : ℕ} {m : ℕ} (hm : 1 ≤ m)
    (u : SobolevSpace n m) (j : Fin n) (i : ℕ) (hi : i ≤ m - 1) :
    MemLp (fun x => iteratedFDeriv ℝ i
      (fun y => fderiv ℝ u.toFun y (EuclideanSpace.single j 1)) x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by

  have hmem := u.iteratedFDeriv_memLp (i + 1) (by omega)

  have hcd_fderiv : ContDiff ℝ (↑i : ℕ∞) (fderiv ℝ u.toFun) := by
    apply u.contDiff_toFun.fderiv_right
    norm_cast; omega

  have hbound : ∀ x : EuclideanSpace ℝ (Fin n),
      ‖iteratedFDeriv ℝ i
        (fun y => fderiv ℝ u.toFun y (EuclideanSpace.single j 1)) x‖ ≤
      ‖EuclideanSpace.single j (1 : ℝ)‖ *
        ‖iteratedFDeriv ℝ (i + 1) u.toFun x‖ := by
    intro x
    have h1 := norm_iteratedFDeriv_clm_apply_const
      (f := fderiv ℝ u.toFun) (c := EuclideanSpace.single j (1 : ℝ)) (x := x)
      hcd_fderiv.contDiffAt (N := (↑i : ℕ∞)) (le_refl _)
    rw [norm_iteratedFDeriv_fderiv] at h1
    exact h1

  exact hmem.of_le_mul
    ((hcd_fderiv.clm_apply contDiff_const).continuous_iteratedFDeriv le_rfl).aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)

end SobolevEmbedding
end
