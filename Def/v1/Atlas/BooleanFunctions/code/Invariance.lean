/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Invariance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.BooleanFunctions.code.LindebergBound
import Theorem.v1.Atlas.BooleanFunctions.code.LindebergOneDim
import Def.v1.Atlas.BooleanFunctions.code.MajorityStablest


noncomputable section

open Finset BigOperators MeasureTheory

namespace BooleanFourier

def linearBooleanFunction {n : ℕ} (a : Fin n → ℝ) : (Fin n → Bool) → ℝ :=
  fun x => ∑ i : Fin n, a i * boolToReal (x i)

noncomputable def singletonCoeffs {n : ℕ} (a : Fin n → ℝ) :
    Finset (Fin n) → ℝ :=
  fun S => if h : ∃ i, S = {i} then a h.choose else 0

def boolCDF {n : ℕ} (f : (Fin n → Bool) → ℝ) (t : ℝ) : ℝ :=
  ((Finset.univ.filter fun x => f x ≤ t).card : ℝ) / (2 : ℝ) ^ n

def HasUnitVariance {n : ℕ} (f : (Fin n → Bool) → ℝ) : Prop :=
  ∑ S : Finset (Fin n), fourierCoeff f S ^ 2 = 1

end BooleanFourier
end
