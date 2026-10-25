/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierL1BoundedC0.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Fourier.RiemannLebesgueLemma


noncomputable section

open MeasureTheory Filter Complex

open scoped FourierTransform RealInnerProductSpace Topology

namespace FourierL1BoundedC0

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

end FourierL1BoundedC0
end
