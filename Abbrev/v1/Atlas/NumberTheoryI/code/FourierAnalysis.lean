/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FourierAnalysis.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Fourier.PoissonSummation
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.MellinTransform
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
open scoped FourierTransform SchwartzMap
open MeasureTheory Complex Real


@[expose] public noncomputable section

namespace FourierAnalysis

abbrev SchwartzSpace := SchwartzMap ℝ ℂ

abbrev mellinTransform (f : ℝ → ℂ) (s : ℂ) : ℂ := mellin f s

open Set Filter Asymptotics in

abbrev gammaFunction (s : ℂ) : ℂ := Complex.Gamma s

end FourierAnalysis
end
