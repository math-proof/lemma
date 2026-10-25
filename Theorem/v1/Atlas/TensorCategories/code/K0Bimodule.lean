/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/K0Bimodule.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TensorCategories.code.GrothendieckRing.Part2
import Lemma.Category.Atlas.v1.TensorCategories.code.GrothendieckRing
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Group.Opposite
import Instance.v1.Atlas.TensorCategories.code.K0Bimodule
set_option maxHeartbeats 800000

open Finset FusionRing


namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : FusionRing ι)

namespace K0Group

variable {R : FusionRing ι}

/-- Each coefficient of the zero element of `K₀(R)` is `0`. -/
@[simp] lemma coeff_zero (k : ι) : (0 : K0Group R).coeff k = 0 := rfl

/-- Addition on `K₀(R)` is computed componentwise. -/
@[simp] lemma coeff_add (a b : K0Group R) (k : ι) :
    (a + b).coeff k = a.coeff k + b.coeff k := rfl

/-- Negation on `K₀(R)` is componentwise. -/
@[simp] lemma coeff_neg (a : K0Group R) (k : ι) :
    (-a).coeff k = -a.coeff k := rfl

/-- Subtraction on `K₀(R)` is computed componentwise. -/
@[simp] lemma coeff_sub (a b : K0Group R) (k : ι) :
    (a - b).coeff k = a.coeff k - b.coeff k := rfl

end K0Group
end FusionRing
