/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/TwoEnds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Combinatorics.Enumerative.DoubleCounting


noncomputable section

open Classical Finset BigOperators

namespace TwoEnds

/-- A point in the Euclidean plane `ℝ²`, modelled as `EuclideanSpace ℝ (Fin 2)`. -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

end TwoEnds
end
