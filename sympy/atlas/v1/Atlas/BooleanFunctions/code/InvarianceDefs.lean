/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/InvarianceDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.BooleanFunctions.code.MultilinearExtension
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.MultilinearExtension
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Talagrand
import sympy.atlas.v1.Atlas.BooleanFunctions.code.Talagrand
import sympy.atlas.v1.Atlas.BooleanFunctions.code.GaussianHypercontractivity
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

noncomputable section

open Finset BigOperators MeasureTheory

namespace BooleanFourier

def booleanExpectation {n : ℕ} (f : (Fin n → Bool) → ℝ) (g : ℝ → ℝ) : ℝ :=
  (1 / (2 : ℝ) ^ n) * ∑ x : Fin n → Bool, g (f x)

def gaussianExpectation {n : ℕ} (f : (Fin n → Bool) → ℝ) (g : ℝ → ℝ) : ℝ :=
  ∫ z : Fin n → ℝ, g (multilinearExtension f z)
    ∂(GaussianHypercontractivity.stdGaussianMeasure n)

structure IsC3Bounded (Ψ : ℝ → ℝ) where
  differentiable : ContDiff ℝ 3 Ψ
  thirdDerivBound : ℝ
  thirdDerivBound_nonneg : 0 ≤ thirdDerivBound
  bound : ∀ x : ℝ, |iteratedDeriv 3 Ψ x| ≤ thirdDerivBound

end BooleanFourier

end
