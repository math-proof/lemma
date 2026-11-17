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
public import Abbrev.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.DecomposingCoveringsAxiom

@[expose] public section

open Set Metric


namespace DecomposingCoverings

/-- Indices of the unit balls that cover a point $x \in \mathbb{R}^3$:
$\{i : x \in B(\text{center}_i, 1)\}$. -/
def coveringSet {ι : Type*} (center : ι → E3) (x : E3) : Set ι :=
  {i | x ∈ Metric.ball (center i) 1}

end DecomposingCoverings
