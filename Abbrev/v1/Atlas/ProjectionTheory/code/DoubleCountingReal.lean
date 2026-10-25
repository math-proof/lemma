/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/DoubleCountingReal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.ProjectionTheory.code.DoubleCountingReal
open Finset BigOperators


namespace ProjectionTheory

/-- A point in the Euclidean plane `ℝ²`, encoded as `Fin 2 → ℝ`. -/
abbrev Point2 := Fin 2 → ℝ

/-- A direction vector in `ℝ²`, encoded as `Fin 2 → ℝ`. -/
abbrev Direction := Fin 2 → ℝ

end ProjectionTheory
