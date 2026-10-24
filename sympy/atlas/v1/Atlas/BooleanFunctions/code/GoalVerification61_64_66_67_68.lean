/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/GoalVerification61_64_66_67_68.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.BooleanFunctions.code.UncoveredBatch2
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Majority
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.BonamilBeckner
import sympy.atlas.v1.Atlas.BooleanFunctions.code.TwoPointInequality
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.TwoPointInequality
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.GaussianSpace
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Claim32Lec8
import sympy.atlas.v1.Atlas.BooleanFunctions.code.GaussianSpace
import sympy.atlas.v1.Atlas.BooleanFunctions.code.Claim32Lec8

open Finset BigOperators Real MeasureTheory


example (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1 / 2) :
    Filter.Tendsto
      (fun k => BooleanFourier.noiseSensitivityReal δ (BooleanFourier.majorityFn (2 * k + 1)))
      Filter.atTop
      (nhds ((1 / Real.pi) * Real.arccos (1 - 2 * δ))) :=
  BooleanFourier.noiseSensitivity_majority_tendsto δ hδ_pos hδ_le


example {n : ℕ} (f : BooleanFourier.BoolFn n)
    {p q ρ : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q) (hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ Real.sqrt ((p - 1) / (q - 1))) :
    BooleanFourier.lpNorm q (BooleanFourier.noiseOp ρ f) ≤ BooleanFourier.lpNorm p f :=
  BooleanFourier.bonami_beckner f hp hpq hρ0 hρ


example {p q ρ : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q) (hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ Real.sqrt ((p - 1) / (q - 1)))
    (g : Bool → ℝ) :
    BooleanFourier.twoPointLpNorm q (BooleanFourier.twoPointNoiseOp ρ g) ≤
      BooleanFourier.twoPointLpNorm p g :=
  BooleanFourier.two_point_inequality hp hpq hρ0 hρ g


example : ∫ t : ℝ, GaussianSpace.stdGaussianDensity t = 1 :=
  GaussianSpace.integral_stdGaussianDensity_eq_one


example {n : ℕ} (hn : n ≠ 0) (A : Finset (Fin n → Bool)) :
    BooleanAnalysis.edgeBoundaryMeasure n A =
      BooleanFourier.totalInfluence (BooleanAnalysis.indicator A) / (n : ℝ) :=
  BooleanAnalysis.edgeBoundaryMeasure_eq_totalInfluence_indicator_div_n hn A
