/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/SchwarzPick.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
open Complex Metric Set Function Filter

open scoped Topology ComplexConjugate


namespace SchwarzPick

noncomputable def mobiusMap (a : ℂ) (w : ℂ) : ℂ :=
  (w - a) / (1 - conj a * w)

noncomputable def mobiusInv (a : ℂ) (w : ℂ) : ℂ :=
  (w + a) / (1 + conj a * w)

noncomputable def hyperbolicDist (z w : ℂ) (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) : ℝ :=
  2 * Real.artanh (‖z - w‖ / ‖starRingEnd ℂ w * z - 1‖)

noncomputable def poincareConformalFactor (z : ℂ) : ℝ :=
  2 / (1 - ‖z‖ ^ 2)

end SchwarzPick
