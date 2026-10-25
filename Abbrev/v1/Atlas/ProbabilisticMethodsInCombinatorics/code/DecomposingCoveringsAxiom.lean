/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/DecomposingCoveringsAxiom.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic
open Set Metric


namespace DecomposingCoverings

/-- Three-dimensional Euclidean space $\mathbb{R}^3$, the ambient space for the
Mani-Levitska–Pach problem on coverings by unit balls. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

end DecomposingCoverings
