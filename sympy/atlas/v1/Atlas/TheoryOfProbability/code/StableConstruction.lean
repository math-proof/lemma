/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/StableConstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import sympy.atlas.v1.Atlas.TheoryOfProbability.code.BochnerTheorem
import sympy.atlas.v1.Atlas.TheoryOfProbability.code.DomainAttraction

open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology ENNReal NNReal

set_option maxHeartbeats 3200000

noncomputable section

namespace ProbabilityTheory
