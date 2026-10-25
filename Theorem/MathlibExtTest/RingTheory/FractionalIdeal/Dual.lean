/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/FractionalIdeal/Dual.lean -/


import Def.RingTheory.FractionalIdeal.Dual.Part2
import Lemma.Int.FractionalIdeal.Dual
open scoped nonZeroDivisors


noncomputable section

variable {A K : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
  [IsFractionRing A K]

example (M : Submodule A K) :
    LinearMap.BilinForm.dualSubmodule
        (LinearMap.mul K K : LinearMap.BilinForm K K) M =
      (1 : Submodule A K) / M :=
  dualSubmodule_mul_eq_div M

example (M : Submodule A K) (hM : M ≠ ⊥) :
    Function.Surjective (LinearMap.BilinForm.dualSubmoduleToDual
      (LinearMap.mul K K : LinearMap.BilinForm K K) M) :=
  Submodule.mul_dualSubmoduleToDual_surjective M hM

example (M : Submodule A K) (hM : M ≠ ⊥) :
    Module.Dual A M ≃ₗ[A] LinearMap.BilinForm.dualSubmodule
      (LinearMap.mul K K : LinearMap.BilinForm K K) M :=
  Submodule.dualEquivMulDualSubmodule M hM

example (M : Submodule A K) (hM : M ≠ ⊥) (f : Module.Dual A M) (m : M) :
    algebraMap A K (f m) =
      (Submodule.dualEquivMulDualSubmodule M hM f : K) * (m : K) :=
  Submodule.dualEquivMulDualSubmodule_spec M hM f m

example (I : FractionalIdeal A⁰ K) (hI : I ≠ 0) :
    ((I⁻¹ : FractionalIdeal A⁰ K) : Submodule A K) =
      LinearMap.BilinForm.dualSubmodule
        (LinearMap.mul K K : LinearMap.BilinForm K K)
        (I : Submodule A K) :=
  FractionalIdeal.coe_inv_eq_mul_dualSubmodule I hI

example (I : FractionalIdeal A⁰ K) (hI : I ≠ 0) :
    Module.Dual A (I : Submodule A K) ≃ₗ[A]
      ((I⁻¹ : FractionalIdeal A⁰ K) : Submodule A K) :=
  FractionalIdeal.dualEquivInv I hI

example (I : FractionalIdeal A⁰ K) (hI : IsUnit I) :
    Module.Dual A (Module.Dual A (I : Submodule A K)) ≃ₗ[A]
      (I : Submodule A K) :=
  FractionalIdeal.doubleDualEquivOfIsUnit I hI

example :
    LinearMap.BilinForm.dualSubmodule
        (LinearMap.mul ℚ ℚ : LinearMap.BilinForm ℚ ℚ)
        ((1 : FractionalIdeal ℤ⁰ ℚ) : Submodule ℤ ℚ) =
      (1 : Submodule ℤ ℚ) / ((1 : FractionalIdeal ℤ⁰ ℚ) : Submodule ℤ ℚ) :=
  dualSubmodule_mul_eq_div ((1 : FractionalIdeal ℤ⁰ ℚ) : Submodule ℤ ℚ)

example : IsUnit (1 : FractionalIdeal ℤ⁰ ℚ) := isUnit_one

example (hI : IsUnit (1 : FractionalIdeal ℤ⁰ ℚ)) :
    Module.Dual ℤ (Module.Dual ℤ
      ((1 : FractionalIdeal ℤ⁰ ℚ) : Submodule ℤ ℚ)) ≃ₗ[ℤ]
      ((1 : FractionalIdeal ℤ⁰ ℚ) : Submodule ℤ ℚ) :=
  FractionalIdeal.doubleDualEquivOfIsUnit 1 hI

end
