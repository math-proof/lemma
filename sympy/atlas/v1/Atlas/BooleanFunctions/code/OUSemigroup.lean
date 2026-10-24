/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/OUSemigroup.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.BooleanFunctions.code.GaussianSpace
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.GaussianSpace
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.MeasureTheory.Integral.Prod

namespace GaussianSpace

open MeasureTheory ProbabilityTheory Real ContinuousLinearMap

section GaussianSumLemma

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def addSmulCLM (a b : ℝ) : (E × E) →L[ℝ] E :=
  a • (ContinuousLinearMap.fst ℝ E E) + b • (ContinuousLinearMap.snd ℝ E E)
