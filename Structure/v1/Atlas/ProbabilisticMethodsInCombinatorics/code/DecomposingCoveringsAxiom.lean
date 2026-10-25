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
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.DecomposingCoveringsAxiom
open Set Metric


namespace DecomposingCoverings

/-- `IsKFoldCovering center k` records that a family of unit balls with centres `center`
is a locally finite $k$-fold covering of $\mathbb{R}^3$: every point is covered at least
$k$ times and only by finitely many balls. -/
structure IsKFoldCovering {ι : Type*} (center : ι → E3) (k : ℕ) : Prop where
  cover : ∀ x : E3, k ≤ (coveringSet center x).ncard
  locallyFinite : ∀ x : E3, (coveringSet center x).Finite

end DecomposingCoverings
