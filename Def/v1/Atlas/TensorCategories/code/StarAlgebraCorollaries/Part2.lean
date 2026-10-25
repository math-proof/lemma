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
import Instance.v1.Atlas.TensorCategories.code.StarAlgebraCorollaries.Part2
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

/-- The ring homomorphism `ℂ →+* GrRingOfC R` sending a scalar `c` to the element supported
at the unit with coefficient `c`. -/
def algebraMapRingHom : ℂ →+* GrRingOfC R where
  toFun c := ⟨fun k => if k = R.unit then c else 0⟩
  map_one' := by ext k; simp
  map_mul' x y := by
    ext k
    change (if k = R.unit then x * y else 0) =
         (R.grMulC (fun k => if k = R.unit then x else 0)
                   (fun k => if k = R.unit then y else 0)) k
    rw [R.grMulC_scalar_left, R.grMulC_one_left]
    split <;> simp_all
  map_zero' := by ext k; simp
  map_add' x y := by
    ext k; change (if k = R.unit then x + y else 0) =
         (if k = R.unit then x else 0) + (if k = R.unit then y else 0)
    split <;> simp

end GrRingOfC
end
end FusionRing
