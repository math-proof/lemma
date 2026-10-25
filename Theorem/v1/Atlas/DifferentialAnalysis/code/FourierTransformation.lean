/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierTransformation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Fourier.LpSpace


noncomputable section

open scoped FourierTransform ComplexInnerProductSpace

open MeasureTheory SchwartzMap

namespace FourierTransformation

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

end FourierTransformation
end
