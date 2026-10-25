import Mathlib
import Lemma.Dieudonne.DatumAndHonda
import Instance.Dieudonne_HondaSelfExt

set_option autoImplicit false

open LinearMap Submodule Function

universe u v

namespace Deformation

namespace HondaSystem

variable {𝓞 : Type u} [CommRing 𝓞] {ℓ : 𝓞} {D : Type v} [AddCommGroup D] [Module 𝓞 D]
  (H : HondaSystem ℓ D)

def extPairs : Submodule 𝓞 (Module.End 𝓞 D × Module.End 𝓞 D) where
  carrier := {XY | H.F ∘ₗ XY.2 + XY.1 ∘ₗ H.V = 0 ∧ H.V ∘ₗ XY.1 + XY.2 ∘ₗ H.F = 0}
  zero_mem' := by simp
  add_mem' {a b} ha hb := by
    obtain ⟨ha₁, ha₂⟩ := ha
    obtain ⟨hb₁, hb₂⟩ := hb
    constructor
    · rw [Prod.snd_add, Prod.fst_add, comp_add, add_comp, add_add_add_comm, ha₁, hb₁, add_zero]
    · rw [Prod.snd_add, Prod.fst_add, comp_add, add_comp, add_add_add_comm, ha₂, hb₂, add_zero]
  smul_mem' c a ha := by
    obtain ⟨ha₁, ha₂⟩ := ha
    constructor
    · rw [Prod.smul_snd, Prod.smul_fst, comp_smul, smul_comp, ← smul_add, ha₁, smul_zero]
    · rw [Prod.smul_snd, Prod.smul_fst, comp_smul, smul_comp, ← smul_add, ha₂, smul_zero]


def filteredEnd : Submodule 𝓞 (Module.End 𝓞 D) where
  carrier := {a | ∀ x ∈ H.L, a x ∈ H.L}
  zero_mem' := fun x _ => by simp
  add_mem' {a b} ha hb := fun x hx => by
    simpa using H.L.add_mem (ha x hx) (hb x hx)
  smul_mem' c a ha := fun x hx => by
    simpa using H.L.smul_mem c (ha x hx)


def innerDerivation : Module.End 𝓞 D →ₗ[𝓞] Module.End 𝓞 D × Module.End 𝓞 D where
  toFun a := (H.F ∘ₗ a - a ∘ₗ H.F, H.V ∘ₗ a - a ∘ₗ H.V)
  map_add' a b := by
    ext x <;> simp [sub_add_sub_comm]
  map_smul' c a := by
    ext x <;> simp [smul_sub]


def innerPairs : Submodule 𝓞 (Module.End 𝓞 D × Module.End 𝓞 D) :=
  H.filteredEnd.map H.innerDerivation

def endHonda : Submodule 𝓞 (Module.End 𝓞 D) :=
  H.filteredEnd ⊓ LinearMap.ker H.innerDerivation


def selfExt : Type v :=
  ↥H.extPairs ⧸ (H.innerPairs.comap H.extPairs.subtype)

end HondaSystem

end Deformation
