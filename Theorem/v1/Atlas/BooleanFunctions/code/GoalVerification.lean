module
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.BonamilBeckner
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.Corollary42Majority
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.Corollary43Majority
public import Def.v1.Atlas.BooleanFunctions.code.Hypercontractivity
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.Hypercontractivity
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.Corollary12Lec9
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.Claim21Lec10
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.Lemma26Lec10
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.GaussianSpace
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.UniqueGames
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.MultilinearExtension
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.NoiseSensitivity
public import Theorem.v1.Atlas.BooleanFunctions.code.Corollary12Lec9
public import Def.v1.Atlas.BooleanFunctions.code.Claim21Lec10
public import Def.v1.Atlas.BooleanFunctions.code.Lemma26Lec10
public import Def.v1.Atlas.BooleanFunctions.code.GaussianSpace
public import Def.v1.Atlas.BooleanFunctions.code.UniqueGames.Part8
public import Theorem.v1.Atlas.BooleanFunctions.code.NoiseSensitivityMonotone
public import Theorem.v1.Atlas.BooleanFunctions.code.BourgainNoiseSensitivity
public import Def.v1.Atlas.BooleanFunctions.code.MultilinearExtension
public import Def.v1.Atlas.BooleanFunctions.code.NoiseSensitivity
open Finset BigOperators Real MeasureTheory ProbabilityTheory


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/GoalVerification.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace BooleanFourier

example {n : ℕ} (ρ : ℝ) (f : BoolFn n) (S : Finset (Fin n)) :
    fourierCoeff (noiseOp ρ f) S = ρ ^ S.card * fourierCoeff f S :=
  noiseOp_fourierCoeff ρ f S


example {n : ℕ} (f : BoolFn n) (hd : degree f ≤ 1) {q : ℝ} (hq : 2 ≤ q) :
    lpNorm q f ≤ Real.sqrt (q - 1) * lpNorm 2 f :=
  lpNorm_degree1_hypercontractive f hd hq


#check @expected_sqrt_sensitivity_lower_bound


#check @bourgain_noise_sensitivity


#check @multilinearExtension


#check @noiseSensitivity


example {n : ℕ} (ρ : ℝ) (i : Fin n) :
    noiseStability ρ (chi ({i} : Finset (Fin n))) = ρ :=
  noiseStability_chi_singleton ρ i


example {n : ℕ} (ρ : ℝ) (i : Fin n) :
    disagreementProb ρ (chi ({i} : Finset (Fin n))) = (1 - ρ) / 2 :=
  disagreementProb_dictator ρ i

end BooleanFourier


#check @ug_hardness_maxcut_of_ugc


#check @GaussianSpace.ornsteinUhlenbeckOp1D

example (ρ : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    GaussianSpace.ornsteinUhlenbeckOp1D ρ f x =
      ∫ z, f (ρ * x + Real.sqrt (1 - ρ ^ 2) * z) ∂(gaussianReal 0 1) :=
  rfl


#check @GaussianSpace.ornsteinUhlenbeck_hermite_1D

