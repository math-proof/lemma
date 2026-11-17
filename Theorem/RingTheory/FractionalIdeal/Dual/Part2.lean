/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/Dual.lean -/
module

public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import Mathlib.RingTheory.FractionalIdeal.Inverse
public import Mathlib.RingTheory.PicardGroup
public import Def.RingTheory.FractionalIdeal.Dual

public section

@[expose] noncomputable section

open scoped nonZeroDivisors
open Module

variable {A K : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]

/-! # Duals of submodules of the fraction field -/


/-- Coe of a nonzero inverse equals the multiplication dual submodule. -/
theorem FractionalIdeal.coe_inv_eq_mul_dualSubmodule
    (I : FractionalIdeal A⁰ K) (hI : I ≠ 0) :
    ((I⁻¹ : FractionalIdeal A⁰ K) : Submodule A K) =
      LinearMap.BilinForm.dualSubmodule
        (LinearMap.mul K K : LinearMap.BilinForm K K)
        (I : Submodule A K) := by
  ext x
  change x ∈ (I⁻¹ : FractionalIdeal A⁰ K) ↔ _
  rw [FractionalIdeal.mem_inv_iff hI]
  simp [LinearMap.BilinForm.mem_dualSubmodule, FractionalIdeal.mem_coe]

