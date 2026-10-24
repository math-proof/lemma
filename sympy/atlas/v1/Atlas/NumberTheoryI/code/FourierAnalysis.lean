/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FourierAnalysis.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

open scoped FourierTransform SchwartzMap
open MeasureTheory Complex Real

noncomputable section

namespace FourierAnalysis

abbrev SchwartzSpace := SchwartzMap ℝ ℂ

abbrev mellinTransform (f : ℝ → ℂ) (s : ℂ) : ℂ := mellin f s

open Set Filter Asymptotics in

abbrev gammaFunction (s : ℂ) : ℂ := Complex.Gamma s
