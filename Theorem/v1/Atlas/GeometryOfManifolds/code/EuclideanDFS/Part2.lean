/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanDFS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.Topology.Algebra.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Normed.Module.Alternating.Curry
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Def.v1.Atlas.GeometryOfManifolds.code.DifferentialForms.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.DifferentialForms
import Def.v1.Atlas.GeometryOfManifolds.code.EuclideanDFS.Part2


noncomputable section

namespace EuclideanΩ

variable {n p : ℕ}

section ContinuousLift

/-- Every alternating multilinear form $f : (\mathbb{R}^n)^p \to \mathbb{R}$ is automatically
continuous, since on the finite-dimensional Euclidean space $\mathbb{R}^n$ it is a finite
polynomial in the coordinates of its arguments. -/
lemma AlternatingMap.continuous_of_euclidean {n p : ℕ}
    (f : Eℝ n [⋀^Fin p]→ₗ[ℝ] ℝ) : Continuous (⇑f : (Fin p → Eℝ n) → ℝ) := by

  have key : ∀ m : Fin p → Eℝ n,
      f m = ∑ r : Fin p → Fin n,
        (∏ i : Fin p, (m i (r i) : ℝ)) *
          f (fun i => EuclideanSpace.single (r i) (1 : ℝ)) := by
    intro m
    have hdecomp : m = fun i => ∑ j : Fin n, m i j • EuclideanSpace.single j (1 : ℝ) := by
      ext i k; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hdecomp]

    change f.toMultilinearMap _ = _
    rw [f.toMultilinearMap.map_sum]
    congr 1; ext r

    change f.toMultilinearMap _ = _
    rw [show (fun i => m i (r i) • EuclideanSpace.single (r i) (1 : ℝ)) =
      (fun i => (m i (r i) : ℝ) • (fun i => EuclideanSpace.single (r i) (1 : ℝ)) i) from rfl]
    rw [f.toMultilinearMap.map_smul_univ]
    simp [smul_eq_mul]

  rw [show ⇑f = (fun m => ∑ r : Fin p → Fin n,
      (∏ i : Fin p, (m i (r i) : ℝ)) *
        f (fun i => EuclideanSpace.single (r i) (1 : ℝ))) from funext key]
  apply continuous_finset_sum _ (fun r _ => ?_)
  apply Continuous.mul
  · apply continuous_finset_prod _ (fun i _ => ?_)
    exact ((EuclideanSpace.proj (r i)).continuous).comp (continuous_apply i)
  · exact continuous_const

end ContinuousLift
end EuclideanΩ
end
