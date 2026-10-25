/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/BourgainLemma.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Order.Filter.Basic
open scoped NNReal ENNReal
open Set


noncomputable section

namespace BourgainUniform

variable {d : ℕ}

/-- The half-open dyadic mesh cube indexed by $k \in \mathbb{Z}^d$ at scale $\delta$:
$\{x : k_i \delta \leq x_i < (k_i+1)\delta\ \forall i\}$. -/
def meshCube (δ : ℝ) (k : Fin d → ℤ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i : Fin d, (k i : ℝ) * δ ≤ x i ∧ x i < ((k i : ℝ) + 1) * δ}

/-- The set of mesh-cube indices $k \in \mathbb{Z}^d$ such that the cube at scale $\delta$
indexed by $k$ has nonempty intersection with $X$. -/
def meshCubesIntersecting (δ : ℝ) (X : Set (EuclideanSpace ℝ (Fin d))) :
    Set (Fin d → ℤ) :=
  {k | (meshCube δ k ∩ X).Nonempty}

/-- The mesh-counting function $|X|_\delta$: the (possibly infinite) number of $\delta$-mesh
cubes that intersect $X$. -/
def meshCount (δ : ℝ) (X : Set (EuclideanSpace ℝ (Fin d))) : ℕ∞ :=
  Set.encard (meshCubesIntersecting δ X)

end BourgainUniform
end
