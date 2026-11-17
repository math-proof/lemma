/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/GaussMapDegree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Structure.v1.Atlas.DifferentialGeometry.code.GaussMapDegree.Part2

@[expose] public section

noncomputable section

open scoped Matrix

namespace GaussMapDegree

def hypersurfaceVolume (n : ℕ) (S : Set (Fin (n + 1) → ℝ)) : ℝ :=
  (MeasureTheory.Measure.hausdorffMeasure (↑n : ℝ) S).toReal

end GaussMapDegree
end
