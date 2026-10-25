-- Carved from Lemma/Definitions/Def_ModularCurve_PDPairing.lean: instance decls only.
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
import Lemma.ModularCurve.PeriodMap
import Lemma.ModularCurve.PDPairing

set_option autoImplicit false

namespace ModularCurve.PDPairing

open Matrix CongruenceSubgroup Matrix.SpecialLinearGroup

open scoped MatrixGroups


section Gamma0Legs

variable (M M' d : ℕ)

instance iotaDeg0_range_finiteIndex [NeZero M'] [NeZero d] (hMM' : M ∣ M') (hdd : d ∣ M' / M) :
    ((iotaDeg0 M M' d hMM' hdd).range).FiniteIndex := by
  haveI : NeZero (M' * d) := ⟨mul_ne_zero (NeZero.ne M') (NeZero.ne d)⟩
  haveI : ((Gamma (M' * d)).subgroupOf (Gamma0 M)).FiniteIndex := inferInstance
  exact Subgroup.finiteIndex_of_le (Gamma_subgroupOf_le_range_iotaDeg0 M M' d hMM' hdd)

end Gamma0Legs

section Gamma0Hecke

variable (M : ℕ)

instance Gamma0Upper_finiteIndex (ℓ : ℕ) [NeZero ℓ] : (Gamma0Upper ℓ).FiniteIndex :=
  (Gamma0Upper_isCongruenceSubgroup ℓ).finiteIndex

variable (ℓ : ℕ)

variable (A : Type*) [AddCommGroup A]

end Gamma0Hecke

section Prim
variable {Φ : Type*} [Group Φ] {R : Type*} [CommRing R]

namespace CentralExt

variable (φ ψ : Additive Φ →+ R)

instance : Mul (CentralExt φ ψ) := ⟨fun x y => (x.1 + y.1 - omega φ ψ x.2 y.2, x.2 * y.2)⟩
instance : One (CentralExt φ ψ) := ⟨((0 : R), (1 : Φ))⟩
instance : Inv (CentralExt φ ψ) := ⟨fun x => (-x.1, x.2⁻¹)⟩

instance : Group (CentralExt φ ψ) where
  mul_assoc x y z := by
    change ((x.1 + y.1 - omega φ ψ x.2 y.2) + z.1 - omega φ ψ (x.2 * y.2) z.2, (x.2 * y.2) * z.2) =
      (x.1 + (y.1 + z.1 - omega φ ψ y.2 z.2) - omega φ ψ x.2 (y.2 * z.2), x.2 * (y.2 * z.2))
    have hc := omega_cocycle φ ψ x.2 y.2 z.2
    refine Prod.ext ?_ (mul_assoc _ _ _)
    change (x.1 + y.1 - omega φ ψ x.2 y.2) + z.1 - omega φ ψ (x.2 * y.2) z.2 =
      x.1 + (y.1 + z.1 - omega φ ψ y.2 z.2) - omega φ ψ x.2 (y.2 * z.2)
    linear_combination (-1 : R) * hc
  one_mul x := by
    change ((0 : R) + x.1 - omega φ ψ 1 x.2, (1 : Φ) * x.2) = x
    rw [omega_one_left, sub_zero, zero_add, one_mul]
    exact Prod.mk.eta
  mul_one x := by
    change (x.1 + 0 - omega φ ψ x.2 1, x.2 * 1) = x
    rw [omega_one_right, sub_zero, add_zero, mul_one]
    exact Prod.mk.eta
  inv_mul_cancel x := by
    change (-x.1 + x.1 - omega φ ψ x.2⁻¹ x.2, x.2⁻¹ * x.2) = ((0 : R), (1 : Φ))
    rw [omega_inv_self, sub_zero, neg_add_cancel, inv_mul_cancel]

end CentralExt

variable [IsFreeGroup Φ]

end Prim

section Cusps

open MulAction

variable (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex] {R : Type*} [CommRing R]

noncomputable instance : Fintype (Cusp Φ) := Fintype.ofFinite _

end Cusps

section Descent

variable (Λ : Subgroup SL(2, ℤ)) [Λ.FiniteIndex] [IsFreeGroup Λ]
variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] {R : Type*} [CommRing R]

instance isFreeGroup_inf : IsFreeGroup ↥(Γ ⊓ Λ) :=
  IsFreeGroup.ofMulEquiv (Subgroup.subgroupOfEquivOfLe (inf_le_right : Γ ⊓ Λ ≤ Λ))

end Descent


end ModularCurve.PDPairing
