/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/InvarianceDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.BooleanFunctions.code.MultilinearExtension
public import Lemma.Bool.Atlas.v1.BooleanFunctions.code.MultilinearExtension
public import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Talagrand
public import Def.v1.Atlas.BooleanFunctions.code.Talagrand
public import Def.v1.Atlas.BooleanFunctions.code.GaussianHypercontractivity
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Def.v1.Atlas.BooleanFunctions.code.InvarianceDefs


public noncomputable section

open Finset BigOperators MeasureTheory

namespace BooleanFourier

structure IsC3Bounded (Ψ : ℝ → ℝ) where
  differentiable : ContDiff ℝ 3 Ψ
  thirdDerivBound : ℝ
  thirdDerivBound_nonneg : 0 ≤ thirdDerivBound
  bound : ∀ x : ℝ, |iteratedDeriv 3 Ψ x| ≤ thirdDerivBound

end BooleanFourier
end
