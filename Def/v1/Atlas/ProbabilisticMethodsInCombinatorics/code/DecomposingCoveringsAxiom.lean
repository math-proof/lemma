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
import Abbrev.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.DecomposingCoveringsAxiom
open Set Metric


namespace DecomposingCoverings

/-- Indices of the unit balls that cover a point $x \in \mathbb{R}^3$:
$\{i : x \in B(\text{center}_i, 1)\}$. -/
def coveringSet {ι : Type*} (center : ι → E3) (x : E3) : Set ι :=
  {i | x ∈ Metric.ball (center i) 1}

end DecomposingCoverings
