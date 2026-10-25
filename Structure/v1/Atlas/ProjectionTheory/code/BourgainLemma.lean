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
import Def.v1.Atlas.ProjectionTheory.code.BourgainLemma
open scoped NNReal ENNReal
open Set


noncomputable section

namespace BourgainUniform

variable {d : ℕ}

/-- `IsUniform Δ m X` is Bourgain's $(\Delta, m)$-uniformity: $X \subset [0,1]^d$, $\Delta = 1/n$
for some $n \in \mathbb{N}$, and for each $j < m$ the number of $\Delta^{j+1}$-mesh cubes
inside any given $\Delta^j$-mesh cube of $X$ is a constant $R_j$ independent of the cube
(the "branching factor" at step $j$). -/
structure IsUniform (Δ : ℝ) (m : ℕ) (X : Set (EuclideanSpace ℝ (Fin d))) : Prop where
  delta_recip_nat : ∃ n : ℕ, 0 < n ∧ Δ = 1 / (n : ℝ)
  subset_unitCube : X ⊆ {x : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ x i ∧ x i ≤ 1}
  branching_uniform : ∀ j : ℕ, j < m →
    ∃ R : ℕ∞, ∀ k ∈ meshCubesIntersecting (Δ ^ j) X,
      meshCount (Δ ^ (j + 1)) (meshCube (Δ ^ j) k ∩ X) = R

end BourgainUniform
end
