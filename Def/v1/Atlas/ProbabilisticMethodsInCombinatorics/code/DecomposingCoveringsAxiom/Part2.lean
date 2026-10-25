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
import Structure.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.DecomposingCoveringsAxiom
open Set Metric


namespace DecomposingCoverings

/-- Multiplicity at $x$: the number of unit balls of the family covering $x$. -/
noncomputable def mult {ι : Type*} (center : ι → E3) (x : E3) : ℕ :=
  (coveringSet center x).ncard

end DecomposingCoverings
