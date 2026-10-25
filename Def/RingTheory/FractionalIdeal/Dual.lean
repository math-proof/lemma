/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/Dual.lean -/

import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.RingTheory.PicardGroup
import Theorem.RingTheory.FractionalIdeal.Dual
@[expose] noncomputable section

open scoped nonZeroDivisors
open Module

variable {A K : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]

/-! # Duals of submodules of the fraction field -/


/-- Dual of a nonzero submodule as the multiplication dual submodule. -/
noncomputable def Submodule.dualEquivMulDualSubmodule (M : Submodule A K) (hM : M ≠ ⊥) :
    Module.Dual A M ≃ₗ[A] LinearMap.BilinForm.dualSubmodule
      (LinearMap.mul K K : LinearMap.BilinForm K K) M :=
  (LinearEquiv.ofBijective (LinearMap.BilinForm.dualSubmoduleToDual
      (LinearMap.mul K K : LinearMap.BilinForm K K) M)
    ⟨LinearMap.BilinForm.dualSubmoduleToDual_injective _
      LinearMap.BilinForm.mul_nondegenerate M
      (Submodule.span_coe_eq_top M hM),
      Submodule.mul_dualSubmoduleToDual_surjective M hM⟩).symm

