/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TensorCategories.code.StarAlgebra
import Lemma.Category.Atlas.v1.TensorCategories.code.StarAlgebra
import Lemma.Category.Atlas.v1.TensorCategories.code.FrobeniusPerron
import Def.v1.Atlas.TensorCategories.code.FrobeniusPerron.Part6
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Instance.v1.Atlas.TensorCategories.code.StarAlgebraCorollaries
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

open Finset Complex

/-- Corollary 1.43.3: a nonzero idempotent in a finite-dimensional `*`-algebra with trace has
positive real trace. -/


namespace StarAlgWithTrace

variable (B : StarAlgWithTrace)

end StarAlgWithTrace

namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : FusionRing ι)

noncomputable section

namespace GrRingOfC

variable {R : FusionRing ι}

/-- Definitional unfolding of the zero coefficient. -/
@[simp] lemma coeff_zero (k : ι) : (0 : GrRingOfC R).coeff k = 0 := rfl

/-- Definitional unfolding of the unit's coefficients. -/
@[simp] lemma coeff_one (k : ι) :
    (1 : GrRingOfC R).coeff k = if k = R.unit then 1 else 0 := rfl

/-- Coefficients distribute over addition. -/
@[simp] lemma coeff_add (a b : GrRingOfC R) (k : ι) :
    (a + b).coeff k = a.coeff k + b.coeff k := rfl

/-- Coefficients commute with negation. -/
@[simp] lemma coeff_neg (a : GrRingOfC R) (k : ι) :
    (-a).coeff k = -a.coeff k := rfl

/-- Coefficients distribute over subtraction. -/
@[simp] lemma coeff_sub (a b : GrRingOfC R) (k : ι) :
    (a - b).coeff k = a.coeff k - b.coeff k := rfl

end GrRingOfC
end
end FusionRing
