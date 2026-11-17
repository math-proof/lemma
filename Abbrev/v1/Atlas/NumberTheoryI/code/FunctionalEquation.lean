/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FunctionalEquation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
open Complex hiding exp continuous_exp
open Real Filter Topology Asymptotics


@[expose] public noncomputable section

namespace FunctionalEquation

abbrev completedZeta (s : ℂ) : ℂ := completedRiemannZeta s

abbrev completedZeta₀ (s : ℂ) : ℂ := completedRiemannZeta₀ s

end FunctionalEquation
end
