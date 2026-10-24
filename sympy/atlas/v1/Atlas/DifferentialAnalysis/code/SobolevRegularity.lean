/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.SobolevDerivatives
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SobolevDerivatives

open MeasureTheory SobolevSpace TemperedDistributions
open scoped FourierTransform SchwartzMap

noncomputable section

namespace SobolevRegularity

variable {n : ℕ}
