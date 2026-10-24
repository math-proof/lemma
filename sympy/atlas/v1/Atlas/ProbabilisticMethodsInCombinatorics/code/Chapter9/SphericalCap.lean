/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/SphericalCap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.InnerProductSpace.PiL2
import sympy.atlas.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter9.LevyIsoperimetric
set_option maxHeartbeats 400000

noncomputable section

open Real Set MeasureTheory

namespace SphericalCap

/-- The $(n-1)$-dimensional Hausdorff measure on the unit sphere $S^{n-1}$, serving as the
unnormalized surface-area measure used to define `normalizedSphereMeasure`. -/
def sphereVolume (n : ℕ) :
    Measure (↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) :=
  Measure.hausdorffMeasure (↑(n - 1) : ℝ)

/-- The total $(n-1)$-Hausdorff surface measure of the sphere $S^{n-1}$ is finite. -/
def normalizedSphereMeasure {n : ℕ}
    (A : Set (↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1))) : ℝ :=
  (sphereVolume n A).toReal / (sphereVolume n Set.univ).toReal

/-- The normalized sphere measure is monotone with respect to set inclusion. -/
def sphericalCapMeasure (n : ℕ) (ε : ℝ) : ℝ :=
  if h : 0 < n then
    normalizedSphereMeasure
      {x : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) |
        (x : EuclideanSpace ℝ (Fin n)) ⟨0, h⟩ ≥ ε}
  else 0

set_option maxHeartbeats 800000 in
