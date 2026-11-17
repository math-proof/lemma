/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/DecomposingCoveringsAxiom.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Real.Basic
@[expose] public section

open Set Metric


namespace DecomposingCoverings

/-- Three-dimensional Euclidean space $\mathbb{R}^3$, the ambient space for the
Mani-Levitska–Pach problem on coverings by unit balls. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

end DecomposingCoverings
