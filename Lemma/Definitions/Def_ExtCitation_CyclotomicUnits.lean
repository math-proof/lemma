import Lemma.Definitions.Def_ClassGroup_GaloisAction
import Lemma.Definitions.Def_Stickelberger_Basic

set_option autoImplicit false

namespace ExtCitation.Cyclotomic

open NumberField JacobiSumStickelberger Stickelberger

variable (p : ℕ) [Fact p.Prime]

section UnitsGalAction

variable (R : Type*) [CommRing R]

noncomputable def unitsEnd (g : R ≃+* R) :
    Module.End (ZMod p) (ModP p (Additive Rˣ)) :=
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  ModP.mapEnd p (MulEquiv.toAdditive (Units.mapEquiv g.toMulEquiv)).toAddMonoidHom

variable {R} in
@[simp] lemma unitsEnd_proj (g : R ≃+* R) (u : Rˣ) :
    unitsEnd p R g (ModP.proj p (Additive Rˣ) (Additive.ofMul u)) =
      ModP.proj p (Additive Rˣ) (Additive.ofMul (Units.mapEquiv g.toMulEquiv u)) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rfl

noncomputable def unitsEndHom : (R ≃+* R) →* Module.End (ZMod p) (ModP p (Additive Rˣ)) where
  toFun := unitsEnd p R
  map_one' := by
    ext a
    obtain ⟨u, rfl⟩ := ModP.proj_surjective p (Additive Rˣ) a
    exact unitsEnd_proj p (RingEquiv.refl R) u.toMul
  map_mul' g h := by
    ext a
    obtain ⟨u, rfl⟩ := ModP.proj_surjective p (Additive Rˣ) a
    simp only [Module.End.mul_apply]
    rfl

end UnitsGalAction

set_option backward.isDefEq.respectTransparency false in

noncomputable instance instIsCycExt :
    IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
  inferInstance

noncomputable def unitsGalAction :
    (ZMod p)ˣ →* Module.End (ZMod p)
      (ModP p (Additive (𝓞 (CyclotomicField p ℚ))ˣ)) :=
  (unitsEndHom p (𝓞 (CyclotomicField p ℚ))).comp (clRingAction p (CyclotomicField p ℚ))

def unitsOmegaEigenspace (i : ℕ) :
    Submodule (ZMod p) (ModP p (Additive (𝓞 (CyclotomicField p ℚ))ˣ)) where
  carrier := {a | IsOmegaEigenvector (unitsGalAction p) i a}
  add_mem' {a b} ha hb d := by
    simp only [Set.mem_setOf_eq, IsOmegaEigenvector] at *
    rw [map_add, ha d, hb d, smul_add]
  zero_mem' d := by simp
  smul_mem' c a ha d := by
    simp only [Set.mem_setOf_eq, IsOmegaEigenvector] at *
    rw [map_smul, ha d, smul_comm]

noncomputable def omegaIdempotent {M : Type*} [AddCommGroup M] [Module (ZMod p) M]
    (ρ : (ZMod p)ˣ →* Module.End (ZMod p) M) (i : ℕ) : Module.End (ZMod p) M :=
  (Nat.card (ZMod p)ˣ : ZMod p)⁻¹ • ∑ d : (ZMod p)ˣ, (((d : ZMod p) ^ i)⁻¹) • ρ d

end ExtCitation.Cyclotomic
