module
public import Def.v1.Atlas.BooleanFunctions.code.MultilinearExtension
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.MultilinearExtension
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.Talagrand
public import Def.v1.Atlas.BooleanFunctions.code.Talagrand
public import Def.v1.Atlas.BooleanFunctions.code.GaussianHypercontractivity
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/InvarianceDefs.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open Finset BigOperators MeasureTheory

namespace BooleanFourier

def booleanExpectation {n : ℕ} (f : (Fin n → Bool) → ℝ) (g : ℝ → ℝ) : ℝ :=
  (1 / (2 : ℝ) ^ n) * ∑ x : Fin n → Bool, g (f x)

def gaussianExpectation {n : ℕ} (f : (Fin n → Bool) → ℝ) (g : ℝ → ℝ) : ℝ :=
  ∫ z : Fin n → ℝ, g (multilinearExtension f z)
    ∂(GaussianHypercontractivity.stdGaussianMeasure n)

end BooleanFourier
end
