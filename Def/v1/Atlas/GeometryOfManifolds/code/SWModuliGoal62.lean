/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SWModuliGoal62.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.FourManifoldsSW.Part8
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.FourManifoldsSW
set_option autoImplicit false


/-- The transition map between two charts $e, e'$ of a charted space, given by $e^{-1}$ followed by $e'$. -/
def chartTransition
    {d : ℕ} {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) N]
    (e e' : atlas (EuclideanSpace ℝ (Fin d)) N) :
    OpenPartialHomeomorph (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)) :=
  e.1.symm.trans e'.1

/-- A chart transition preserves orientation iff its Jacobian determinant is positive everywhere on its source. -/
def chartTransitionPreservesOrientation
    {d : ℕ} {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) N]
    (e e' : atlas (EuclideanSpace ℝ (Fin d)) N) : Prop :=
  ∀ x ∈ (chartTransition e e').source,
    0 < (fderivWithin ℝ (chartTransition e e') (chartTransition e e').source x).det

/-- A $d$-dimensional charted space is orientable when every pair of chart transitions has positive Jacobian determinant. -/
def IsOrientableManifold
    (d : ℕ) (N : Type*) [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) N] : Prop :=
  ∀ (e e' : atlas (EuclideanSpace ℝ (Fin d)) N),
    chartTransitionPreservesOrientation e e'


