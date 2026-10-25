/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MultifusionSemisimple.lean -/

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
import Instance.v1.Atlas.TensorCategories.code.MultifusionSemisimple
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

open Finset Complex


namespace MultifusionRingDef

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (M : MultifusionRingDef ι)

noncomputable section

namespace MfGrRingOfC

variable {M : MultifusionRingDef ι}

/-- Coordinates of the zero element vanish. -/
@[simp] lemma coeff_zero (k : ι) : (0 : MfGrRingOfC M).coeff k = 0 := rfl

/-- Coordinates of the unit element are the indicator function of `I₀`. -/
@[simp] lemma coeff_one (k : ι) :
    (1 : MfGrRingOfC M).coeff k = if k ∈ M.I₀ then 1 else 0 := rfl

/-- Coordinates of a sum are the sum of coordinates. -/
@[simp] lemma coeff_add (a b : MfGrRingOfC M) (k : ι) :
    (a + b).coeff k = a.coeff k + b.coeff k := rfl

/-- Coordinates of a negation are the negation of coordinates. -/
@[simp] lemma coeff_neg (a : MfGrRingOfC M) (k : ι) :
    (-a).coeff k = -a.coeff k := rfl

/-- Coordinates of a difference are the coordinate-wise difference. -/
@[simp] lemma coeff_sub (a b : MfGrRingOfC M) (k : ι) :
    (a - b).coeff k = a.coeff k - b.coeff k := rfl

end MfGrRingOfC
end
end MultifusionRingDef
