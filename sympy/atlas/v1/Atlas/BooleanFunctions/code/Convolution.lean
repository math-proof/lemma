/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Convolution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.BooleanFunctions.code.FourierExpansion
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.FourierExpansion

open Finset BigOperators

namespace BooleanFourier

def boolMul {n : ℕ} (x y : Fin n → Bool) : Fin n → Bool :=
  fun i => !(x i ^^ y i)

noncomputable def conv {n : ℕ} (f g : (Fin n → Bool) → ℝ) :
    (Fin n → Bool) → ℝ :=
  fun x => (1 / (2 : ℝ) ^ n) * ∑ y : Fin n → Bool, f y * g (boolMul x y)
