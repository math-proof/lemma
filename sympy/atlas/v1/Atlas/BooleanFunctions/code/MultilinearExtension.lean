/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/MultilinearExtension.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.BooleanFunctions.code.FourierExpansion
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.FourierExpansion
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Stability
import sympy.atlas.v1.Atlas.BooleanFunctions.code.Stability

open Finset BigOperators

namespace BooleanFourier

noncomputable def multilinearExtension {n : ℕ} (f : (Fin n → Bool) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ S : Finset (Fin n), fourierCoeff f S * ∏ i ∈ S, x i
