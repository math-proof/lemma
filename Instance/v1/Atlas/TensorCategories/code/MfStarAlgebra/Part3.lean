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
import Def.v1.Atlas.TensorCategories.code.MfStarAlgebra.Part2
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

open Finset Complex


namespace MultifusionRingDef

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : MultifusionRingDef ι)

noncomputable section

namespace MfGrRingOfC

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {R : MultifusionRingDef ι}

/-- The complexified Grothendieck ring of a multifusion ring is a `ℂ`-algebra. -/
noncomputable instance instAlgebra : Algebra ℂ (MfGrRingOfC R) where
  smul c a := ⟨fun k => c * a.coeff k⟩
  algebraMap := algebraMapRingHom
  commutes' c a := by
    ext k
    change (R.mfGrMulC (fun k => if k ∈ R.I₀ then c else 0) a.coeff) k =
         (R.mfGrMulC a.coeff (fun k => if k ∈ R.I₀ then c else 0)) k
    rw [R.mfGrMulC_scalar_left, R.mfGrMulC_one_left,
        R.mfGrMulC_scalar_right, R.mfGrMulC_one_right]
  smul_def' c a := by
    ext k
    change c * a.coeff k =
         (R.mfGrMulC (fun k => if k ∈ R.I₀ then c else 0) a.coeff) k
    rw [R.mfGrMulC_scalar_left, R.mfGrMulC_one_left]

/-- Star-ring structure on the complexified Grothendieck ring: the anti-involution
given by complex conjugation composed with duality. -/
noncomputable instance instStarRing : StarRing (MfGrRingOfC R) where
  star a := ⟨R.mfGrStarC a.coeff⟩
  star_involutive a := by
    ext k
    show R.mfGrStarC (R.mfGrStarC a.coeff) k = a.coeff k
    unfold MultifusionRingDef.mfGrStarC
    simp [R.star_star]
  star_mul a b := by
    ext k
    change R.mfGrStarC (R.mfGrMulC a.coeff b.coeff) k =
         (R.mfGrMulC (R.mfGrStarC b.coeff) (R.mfGrStarC a.coeff)) k
    unfold MultifusionRingDef.mfGrStarC MultifusionRingDef.mfGrMulC
    simp only [map_sum, map_mul, Complex.conj_natCast]
    conv_rhs =>
      rw [← Equiv.sum_comp R.mfStarEquiv]
      arg 2; ext p; rw [← Equiv.sum_comp R.mfStarEquiv]
    simp only [MultifusionRingDef.mfStarEquiv, Equiv.coe_fn_mk, R.star_star]
    conv_rhs =>
      arg 2; ext j; arg 2; ext i
      rw [show R.N (R.star j) (R.star i) k = R.N i j (R.star k) from R.mf_N_star_reverse i j k]
    rw [Finset.sum_comm]
    congr 1; ext i; congr 1; ext j; ring
  star_add a b := by
    ext k
    show R.mfGrStarC (fun k => a.coeff k + b.coeff k) k =
         R.mfGrStarC a.coeff k + R.mfGrStarC b.coeff k
    unfold MultifusionRingDef.mfGrStarC; simp [map_add]

/-- Compatibility of the star and the `ℂ`-scalar action on the complexified Grothendieck ring. -/
noncomputable instance instStarModule : StarModule ℂ (MfGrRingOfC R) where
  star_smul c a := by
    ext k
    show R.mfGrStarC (fun k => c * a.coeff k) k =
         (starRingEnd ℂ c) * R.mfGrStarC a.coeff k
    unfold MultifusionRingDef.mfGrStarC
    simp [map_mul]

/-- The complexified Grothendieck ring is finite-dimensional over `ℂ`. -/
noncomputable instance instFiniteDimensional : FiniteDimensional ℂ (MfGrRingOfC R) := by
  apply FiniteDimensional.of_surjective
    (show (ι → ℂ) →ₗ[ℂ] MfGrRingOfC R from
      { toFun := fun f => ⟨f⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun c f => rfl })
    (fun ⟨f⟩ => ⟨f, rfl⟩)

end MfGrRingOfC
end
end MultifusionRingDef
