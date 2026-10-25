/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/Dual.lean -/

import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.RingTheory.PicardGroup
import Theorem.RingTheory.FractionalIdeal.Dual.Part2
@[expose] noncomputable section

open scoped nonZeroDivisors
open Module

variable {A K : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]

/-! # Duals of submodules of the fraction field -/


/-- Dual of a nonzero fractional ideal is its inverse submodule. -/
noncomputable def FractionalIdeal.dualEquivInv
    (I : FractionalIdeal A⁰ K) (hI : I ≠ 0) :
    Module.Dual A (I : Submodule A K) ≃ₗ[A]
      ((I⁻¹ : FractionalIdeal A⁰ K) : Submodule A K) := by
  have hM : (I : Submodule A K) ≠ ⊥ :=
    FractionalIdeal.coeToSubmodule_ne_bot.mpr hI
  exact (Submodule.dualEquivMulDualSubmodule (I : Submodule A K) hM).trans
    (LinearEquiv.ofEq _ _
      (FractionalIdeal.coe_inv_eq_mul_dualSubmodule I hI).symm)

/-- Double dual of a unit fractional ideal is the ideal itself. -/
noncomputable def FractionalIdeal.doubleDualEquivOfIsUnit
    (I : FractionalIdeal A⁰ K) (hI : IsUnit I) :
    Module.Dual A (Module.Dual A (I : Submodule A K)) ≃ₗ[A]
      (I : Submodule A K) := by
  haveI : Module.Finite A (I : Submodule A K) :=
    Module.Finite.of_fg (FractionalIdeal.fg_of_isUnit I hI)
  have hcoe : IsUnit (I : Submodule A K) :=
    hI.map (FractionalIdeal.coeSubmoduleHom A⁰ K)
  haveI : Module.Projective A (I : Submodule A K) := by
    apply Submodule.projective_of_isUnit
    exact hcoe
  exact (Module.evalEquiv A (I : Submodule A K)).symm

