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
import Instance.v1.Atlas.TensorCategories.code.MfStarAlgebra.Part2
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

open Finset Complex


namespace MultifusionRingDef

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : MultifusionRingDef ι)

noncomputable section

namespace MfGrRingOfC

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {R : MultifusionRingDef ι}

/-- The ring homomorphism `ℂ →+* MfGrRingOfC R` sending `c` to the constant `c` on `R.I₀`. -/
noncomputable def algebraMapRingHom : ℂ →+* MfGrRingOfC R where
  toFun c := ⟨fun k => if k ∈ R.I₀ then c else 0⟩
  map_one' := by ext k; simp [MultifusionRingDef.mfOneC]
  map_mul' x y := by
    ext k
    change (if k ∈ R.I₀ then x * y else 0) =
         (R.mfGrMulC (fun k => if k ∈ R.I₀ then x else 0)
                   (fun k => if k ∈ R.I₀ then y else 0)) k
    rw [R.mfGrMulC_scalar_left, R.mfGrMulC_one_left]
    split <;> simp_all
  map_zero' := by ext k; simp
  map_add' x y := by
    ext k; change (if k ∈ R.I₀ then x + y else 0) =
         (if k ∈ R.I₀ then x else 0) + (if k ∈ R.I₀ then y else 0)
    split <;> simp

end MfGrRingOfC
end
end MultifusionRingDef
