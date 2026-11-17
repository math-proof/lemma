/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/BourgainLemma.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Order.Filter.Basic
public import Structure.v1.Atlas.ProjectionTheory.code.BourgainLemma

@[expose] public section

open scoped NNReal ENNReal
open Set


noncomputable section

namespace BourgainUniform

variable {d : ℕ}

/-- `IsRegularSet δ s C X` says that $X$ is a $(\delta, s, C)$-regular set: for every scale
$\rho \in [\delta, 1]$ and every $\rho$-mesh cube $Q$, $|X \cap Q|_\delta \leq C \rho^s |X|_\delta$,
the discrete analogue of Frostman regularity with exponent $s$. -/
def IsRegularSet (δ : ℝ) (s : ℝ) (C : NNReal) (X : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ (ρ : ℝ), δ ≤ ρ → ρ ≤ 1 →
    ∀ k ∈ meshCubesIntersecting ρ X,
      (meshCount δ (meshCube ρ k ∩ X) : ENNReal) ≤
        C * (ENNReal.ofReal ρ) ^ s * (meshCount δ X : ENNReal)

end BourgainUniform
end
