/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/GaussMap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
@[expose] public noncomputable section



open Metric Set

namespace GaussMap

variable {n : ℕ}

abbrev unitSphere (n : ℕ) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1


end GaussMap
end
