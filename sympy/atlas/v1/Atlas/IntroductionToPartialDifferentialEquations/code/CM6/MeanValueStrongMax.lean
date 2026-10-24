/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM6/MeanValueStrongMax.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM7.LaplaceProperties
import Lemma.Real.Atlas.v1.IntroductionToPartialDifferentialEquations.code.CM7.LaplaceProperties
import Mathlib.MeasureTheory.Measure.Hausdorff

open Set Metric MeasureTheory

noncomputable section

namespace CM6
