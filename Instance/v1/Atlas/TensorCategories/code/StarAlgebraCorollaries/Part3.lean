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
import Def.v1.Atlas.TensorCategories.code.StarAlgebraCorollaries.Part2
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

/-- `GrRingOfC R` is a ℂ-algebra via the canonical inclusion `c ↦ c * 1`. -/
instance instAlgebra : Algebra ℂ (GrRingOfC R) where
  smul c a := ⟨fun k => c * a.coeff k⟩
  algebraMap := algebraMapRingHom
  commutes' c a := by
    ext k
    change (R.grMulC (fun k => if k = R.unit then c else 0) a.coeff) k =
         (R.grMulC a.coeff (fun k => if k = R.unit then c else 0)) k
    rw [R.grMulC_scalar_left, R.grMulC_one_left,
        R.grMulC_scalar_right, R.grMulC_one_right]
  smul_def' c a := by
    ext k
    change c * a.coeff k =
         (R.grMulC (fun k => if k = R.unit then c else 0) a.coeff) k
    rw [R.grMulC_scalar_left, R.grMulC_one_left]

/-- The star-ring structure on `GrRingOfC R` defined via the index-dualising involution
`grStarC`. -/
instance instStarRing : StarRing (GrRingOfC R) where
  star a := ⟨R.grStarC a.coeff⟩
  star_involutive a := by
    ext k
    show R.grStarC (R.grStarC a.coeff) k = a.coeff k
    unfold grStarC
    simp [R.star_star]
  star_mul a b := by
    ext k
    change R.grStarC (R.grMulC a.coeff b.coeff) k =
         (R.grMulC (R.grStarC b.coeff) (R.grStarC a.coeff)) k
    unfold grStarC grMulC


    simp only [map_sum, map_mul, Complex.conj_natCast]

    conv_rhs =>
      rw [← Equiv.sum_comp R.starEquivC]
      arg 2; ext p; rw [← Equiv.sum_comp R.starEquivC]
    simp only [starEquivC, Equiv.coe_fn_mk, R.star_star]


    conv_rhs =>
      arg 2; ext j; arg 2; ext i
      rw [show R.N (R.star j) (R.star i) k = R.N i j (R.star k) from R.N_star_reverse i j k]


    rw [Finset.sum_comm]


    congr 1; ext i; congr 1; ext j; ring
  star_add a b := by
    ext k
    show R.grStarC (fun k => a.coeff k + b.coeff k) k =
         R.grStarC a.coeff k + R.grStarC b.coeff k
    unfold grStarC; simp [map_add]

/-- The star-module compatibility on `GrRingOfC R` over ℂ: `star (c • a) = conj c • star a`. -/
instance instStarModule : StarModule ℂ (GrRingOfC R) where
  star_smul c a := by
    ext k
    show R.grStarC (fun k => c * a.coeff k) k =
         (starRingEnd ℂ c) * R.grStarC a.coeff k
    unfold grStarC
    simp [map_mul]

/-- `GrRingOfC R` is finite-dimensional as a ℂ-vector space (since `ι` is finite). -/
instance instFiniteDimensional : FiniteDimensional ℂ (GrRingOfC R) := by
  apply FiniteDimensional.of_surjective
    (show (ι → ℂ) →ₗ[ℂ] GrRingOfC R from
      { toFun := fun f => ⟨f⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun c f => rfl })
    (fun ⟨f⟩ => ⟨f, rfl⟩)

end GrRingOfC
end
end FusionRing
