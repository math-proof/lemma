import Mathlib
import Lemma.Dieudonne.DatumAndHonda
import Instance.Dieudonne_HondaSelfExt
import Def.Dieudonne_HondaSelfExt

set_option autoImplicit false

open LinearMap Submodule Function

universe u v

namespace Deformation

namespace HondaSystem

variable {𝓞 : Type u} [CommRing 𝓞] {ℓ : 𝓞} {D : Type v} [AddCommGroup D] [Module 𝓞 D]
  (H : HondaSystem ℓ D)


theorem mem_extPairs_iff (XY : Module.End 𝓞 D × Module.End 𝓞 D) :
    XY ∈ H.extPairs ↔ H.F ∘ₗ XY.2 + XY.1 ∘ₗ H.V = 0 ∧ H.V ∘ₗ XY.1 + XY.2 ∘ₗ H.F = 0 :=
  Iff.rfl


theorem mem_filteredEnd_iff (a : Module.End 𝓞 D) :
    a ∈ H.filteredEnd ↔ ∀ x ∈ H.L, a x ∈ H.L :=
  Iff.rfl


theorem innerDerivation_apply (a : Module.End 𝓞 D) :
    H.innerDerivation a = (H.F ∘ₗ a - a ∘ₗ H.F, H.V ∘ₗ a - a ∘ₗ H.V) :=
  rfl


theorem mem_endHonda_iff (a : Module.End 𝓞 D) :
    a ∈ H.endHonda ↔ (∀ x ∈ H.L, a x ∈ H.L) ∧ H.F ∘ₗ a = a ∘ₗ H.F ∧ H.V ∘ₗ a = a ∘ₗ H.V := by
  simp only [endHonda, Submodule.mem_inf, mem_filteredEnd_iff, LinearMap.mem_ker,
    innerDerivation_apply, Prod.mk_eq_zero, sub_eq_zero]

theorem innerPairs_le_extPairs : H.innerPairs ≤ H.extPairs := by
  rintro _ ⟨a, -, rfl⟩
  rw [mem_extPairs_iff, innerDerivation_apply]
  constructor
  · ext x
    simp [H.toDieudonneDatum.F_V_apply]
  · ext x
    simp [H.toDieudonneDatum.V_F_apply]

end HondaSystem

end Deformation
