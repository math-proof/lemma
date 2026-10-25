/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/FourierBoundReal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.ProjectionTheory.code.HausdorffSpacing
import Def.v1.Atlas.ProjectionTheory.code.OSRW
import Structure.v1.Atlas.ProjectionTheory.code.DoubleCountingRealCor
import Lemma.Real.Atlas.v1.ProjectionTheory.code.DoubleCountingRealCor


namespace ProjectionTheory

open Finset

/-- Shorthand for the Euclidean plane `ℝ²` with its standard inner product. -/
noncomputable abbrev ℝ2 := EuclideanSpace ℝ (Fin 2)

end ProjectionTheory
