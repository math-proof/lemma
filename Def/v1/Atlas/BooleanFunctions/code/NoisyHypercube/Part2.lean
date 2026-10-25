/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/NoisyHypercube.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.BooleanFunctions.code.FourierExpansion
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.FourierExpansion
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Structure.v1.Atlas.BooleanFunctions.code.NoisyHypercube
open Finset BigOperators


namespace BooleanFourier

noncomputable def noisyHypercubeTransitionProb {n : ℕ} (ρ : ℝ) (_hρ₀ : 0 ≤ ρ) (_hρ₁ : ρ ≤ 1)
    (x y : Fin n → Bool) : ℝ :=
  ∏ i : Fin n, ((1 + ρ * (boolToReal (x i) * boolToReal (y i))) / 2)

noncomputable def NoisyHypercube.transitionProb (G : NoisyHypercube) (x y : Fin G.n → Bool) : ℝ :=
  noisyHypercubeTransitionProb G.ρ G.hρ_nonneg G.hρ_le_one x y

noncomputable def noiseOpProb {n : ℕ} (ρ : ℝ) (f : (Fin n → Bool) → ℝ) :
    (Fin n → Bool) → ℝ := fun x =>
  ∑ y : Fin n → Bool,
    (∏ i : Fin n, ((1 + ρ * (boolToReal (x i) * boolToReal (y i))) / 2)) * f y

end BooleanFourier
