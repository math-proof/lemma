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
import Instance.v1.Atlas.TensorCategories.code.K0Bimodule.Part4
set_option maxHeartbeats 800000

open Finset FusionRing


namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : FusionRing ι)

/-- Coefficients of the right scalar product are computed by `k0ActRight`. -/
@[simp] lemma smul_right_coeff (r : (GrRingOf R)ᵐᵒᵖ) (m : K0Group R) (k : ι) :
    (r • m).coeff k = R.k0ActRight m.coeff r.unop.coeff k := rfl

end FusionRing
