/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/GaussMapDegree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Hausdorff
import Structure.v1.Atlas.DifferentialGeometry.code.GaussMapDegree.Part2


noncomputable section

open scoped Matrix

namespace GaussMapDegree

def hypersurfaceVolume (n : ℕ) (S : Set (Fin (n + 1) → ℝ)) : ℝ :=
  (MeasureTheory.Measure.hausdorffMeasure (↑n : ℝ) S).toReal

end GaussMapDegree
end
