/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/FourierSeries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.FourierAnalysis.code.FourierSeries
open MeasureTheory MeasureTheory.Measure AddCircle
open scoped ENNReal NNReal Convolution

open MeasureTheory Filter Topology Set intervalIntegral Real

open ContinuousMap Set

open MeasureTheory Filter Topology Set intervalIntegral Real


noncomputable section

namespace FejerL1Density

noncomputable instance : Fact (0 < (2 * π : ℝ)) := ⟨by positivity⟩

end FejerL1Density
end
