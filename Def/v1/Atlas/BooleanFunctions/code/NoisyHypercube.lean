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
open Finset BigOperators


namespace BooleanFourier

noncomputable def correlatedPairProb (ρ : ℝ) (_hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    (a b : Bool) : ℝ :=
  (1 + ρ * (boolToReal a * boolToReal b)) / 2

noncomputable def correlatedProb {n : ℕ} (ρ : ℝ) (_hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    (x y : Fin n → Bool) : ℝ :=
  ∏ i : Fin n, (1 + ρ * (boolToReal (x i) * boolToReal (y i))) / 2

end BooleanFourier
