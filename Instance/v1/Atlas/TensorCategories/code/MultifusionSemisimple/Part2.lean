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
import Theorem.v1.Atlas.TensorCategories.code.MultifusionSemisimple
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

open Finset Complex


namespace MultifusionRingDef

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (M : MultifusionRingDef ι)

noncomputable section

namespace MfGrRingOfC

variable {M : MultifusionRingDef ι}

/-- Ring structure on `MfGrRingOfC M`: coordinate-wise additive group with multiplication
given by the multifusion structure constants. -/
instance instStarRing : StarRing (MfGrRingOfC M) where
  star a := ⟨M.mfGrStarC a.coeff⟩
  star_involutive a := by
    ext k
    show M.mfGrStarC (M.mfGrStarC a.coeff) k = a.coeff k
    unfold mfGrStarC
    simp [M.star_star]
  star_mul a b := by
    ext k
    change M.mfGrStarC (M.mfGrMulC a.coeff b.coeff) k =
         (M.mfGrMulC (M.mfGrStarC b.coeff) (M.mfGrStarC a.coeff)) k
    unfold mfGrStarC mfGrMulC
    simp only [map_sum, map_mul, Complex.conj_natCast]
    conv_rhs =>
      rw [← Equiv.sum_comp M.mfStarEquiv]
      arg 2; ext p; rw [← Equiv.sum_comp M.mfStarEquiv]
    simp only [mfStarEquiv, Equiv.coe_fn_mk, M.star_star]
    conv_rhs =>
      arg 2; ext j; arg 2; ext i
      rw [show M.N (M.star j) (M.star i) k = M.N i j (M.star k) from by
        rw [M.star_anti]; simp [M.star_star]]
    rw [Finset.sum_comm]
    congr 1; ext i; congr 1; ext j; ring
  star_add a b := by
    ext k
    show M.mfGrStarC (fun k => a.coeff k + b.coeff k) k =
         M.mfGrStarC a.coeff k + M.mfGrStarC b.coeff k
    unfold mfGrStarC; simp [map_add]

/-- Compatibility of star and scalar multiplication: `star (c • a) = (conj c) • star a`. -/
instance instStarModule : StarModule ℂ (MfGrRingOfC M) where
  star_smul c a := by
    ext k
    show M.mfGrStarC (fun k => c * a.coeff k) k =
         (starRingEnd ℂ c) * M.mfGrStarC a.coeff k
    unfold mfGrStarC
    simp [map_mul]

/-- The complexified multifusion Grothendieck ring `MfGrRingOfC M` is finite-dimensional
over `ℂ`, with dimension at most `|ι|`. -/
instance instFiniteDimensional : FiniteDimensional ℂ (MfGrRingOfC M) := by
  apply FiniteDimensional.of_surjective
    (show (ι → ℂ) →ₗ[ℂ] MfGrRingOfC M from
      { toFun := fun f => ⟨f⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun c f => rfl })
    (fun ⟨f⟩ => ⟨f, rfl⟩)

end MfGrRingOfC
end
end MultifusionRingDef
