/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Claim21Lec10.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.BooleanFunctions.code.Stability
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Stability
import Def.v1.Atlas.BooleanFunctions.code.GaussianStability.Part2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.Basic
open Finset BigOperators Real Filter


namespace BooleanFourier

noncomputable def majorityFn (n : ℕ) : (Fin n → Bool) → ℝ := fun x =>
  if 2 * (Finset.univ.filter (fun i => x i = true)).card > n then 1 else -1

noncomputable def BooleanFourier.signFn : ℝ → ℝ := fun x => if x ≥ 0 then 1 else -1

noncomputable def BooleanFourier.gaussianSignCorrelation (ρ : ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, BooleanFourier.signFn p.1 * BooleanFourier.signFn p.2
    ∂(GaussianStability.rhoCorrelatedGaussian ρ)


end BooleanFourier
