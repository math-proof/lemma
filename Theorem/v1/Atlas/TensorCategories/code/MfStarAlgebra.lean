/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MfStarAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TensorCategories.code.StarAlgebra
import Lemma.Category.Atlas.v1.TensorCategories.code.StarAlgebra
import Lemma.Category.Atlas.v1.TensorCategories.code.BasedRings
import Abbrev.v1.Atlas.TensorCategories.code.BasedRings
import Mathlib.LinearAlgebra.Dimension.Finrank
import Instance.v1.Atlas.TensorCategories.code.MfStarAlgebra
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

open Finset Complex


namespace MultifusionRingDef

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : MultifusionRingDef ι)

noncomputable section

namespace MfGrRingOfC

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {R : MultifusionRingDef ι}

/-- The coefficients of the zero element of the complexified Grothendieck ring are zero. -/
@[simp] lemma coeff_zero (k : ι) : (0 : MfGrRingOfC R).coeff k = 0 := rfl

/-- The coefficients of the unit element are `1` on `R.I₀` and `0` elsewhere. -/
@[simp] lemma coeff_one (k : ι) :
    (1 : MfGrRingOfC R).coeff k = if k ∈ R.I₀ then 1 else 0 := rfl

/-- Addition on the complexified Grothendieck ring is componentwise on coefficients. -/
@[simp] lemma coeff_add (a b : MfGrRingOfC R) (k : ι) :
    (a + b).coeff k = a.coeff k + b.coeff k := rfl

/-- Negation on the complexified Grothendieck ring is componentwise on coefficients. -/
@[simp] lemma coeff_neg (a : MfGrRingOfC R) (k : ι) :
    (-a).coeff k = -a.coeff k := rfl

/-- Subtraction on the complexified Grothendieck ring is componentwise on coefficients. -/
@[simp] lemma coeff_sub (a b : MfGrRingOfC R) (k : ι) :
    (a - b).coeff k = a.coeff k - b.coeff k := rfl

end MfGrRingOfC
end
end MultifusionRingDef
