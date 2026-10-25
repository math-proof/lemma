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

/-- The complex basis vector concentrated at index `i`. -/
def basisVecC (i : ι) : ι → ℂ :=
  fun k => if k = i then 1 else 0

/-- Iterated multiplication of `f : ι → ℂ` with itself in the complexified Grothendieck ring,
starting from the multiplicative unit at exponent 0. -/
def grPowC (R : FusionRing ι) (f : ι → ℂ) : ℕ → (ι → ℂ)
  | 0 => fun k => if k = R.unit then 1 else 0
  | n + 1 => R.grMulC (grPowC R f n) f

end
end FusionRing
