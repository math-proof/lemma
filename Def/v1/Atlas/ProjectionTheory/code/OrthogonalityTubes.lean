/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/OrthogonalityTubes.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


noncomputable section

namespace OrthogonalityTubes

open MeasureTheory

/-- The perpendicular vector in $\mathbb{R}^2$: $\mathrm{perp}(d_0, d_1) = (-d_1, d_0)$. -/
def perp (d : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-(d 1), d 0]

/-- Underlying point set of a rectangle with centre $c$, axis-direction $d$, width $w$ and
length $l$: the set of $x$ with $|\langle x - c, d\rangle| \le l/2$ and
$|\langle x - c, d^\perp\rangle| \le w/2$. -/
def rectangleCarrier (c d : EuclideanSpace ℝ (Fin 2)) (w l : ℝ) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | |@inner ℝ _ _ (x - c) d| ≤ l / 2 ∧ |@inner ℝ _ _ (x - c) (perp d)| ≤ w / 2}

end OrthogonalityTubes
end
