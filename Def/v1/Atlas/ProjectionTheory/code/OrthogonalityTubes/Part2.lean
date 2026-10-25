/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/OrthogonalityTubes.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.v1.Atlas.ProjectionTheory.code.OrthogonalityTubes


noncomputable section

namespace OrthogonalityTubes

open MeasureTheory

/-- The underlying point set of a tube $T$: the $1 \times R$ rectangle with axis along
`T.direction` centred at `T.center`. -/
def Tube.carrier {R : ℝ} (T : Tube R) : Set (EuclideanSpace ℝ (Fin 2)) :=
  rectangleCarrier T.center T.direction 1 R

/-- The open $r$-thickening of a tube's carrier (the set of points within distance $r$). -/
def Tube.rNeighborhood {R : ℝ} (T : Tube R) (r : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  Metric.thickening r T.carrier

end OrthogonalityTubes
end
