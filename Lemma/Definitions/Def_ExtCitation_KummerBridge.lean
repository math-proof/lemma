import Lemma.Definitions.Def_ExtCitation_AdmissibleExtension

set_option autoImplicit false

universe u

namespace groupCohomology

variable {Γ : Type*} [Group Γ] {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable [DistribMulAction Γ V] [SMulCommClass Γ R V]

def extClassFun (χ : Γ →* Rˣ) (v₀ : V) (σ : Γ) : V :=
  (((χ σ)⁻¹ : Rˣ) : R) • (σ • v₀ - (χ σ : R) • v₀)

omit [SMulCommClass Γ R V] in

lemma extClassFun_mem (χ : Γ →* Rˣ) (v₀ : V) (C : Submodule R V)
    (hquot : ∀ σ : Γ, ∀ x : V, σ • x - (χ σ : R) • x ∈ C) (σ : Γ) :
    extClassFun χ v₀ σ ∈ C :=
  C.smul_mem _ (hquot σ v₀)

end groupCohomology

namespace ExtCitation

variable (p : ℕ) [Fact p.Prime]

noncomputable def cycloChar :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod p)ˣ :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  MonoidHom.mk'
    (fun σ => modularCyclotomicCharacter (AlgebraicClosure ℚ) (card_rootsOfUnity_eq_self p)
      (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ))
    (fun a b => by rw [← map_mul]; congr 1)

lemma val_cycloChar (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ((cycloChar p σ : ZMod p) : ZMod p).val = cycloExp p σ := rfl

lemma coe_cycloChar (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ((cycloChar p σ : ZMod p)) = (cycloExp p σ : ZMod p) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [← val_cycloChar, ZMod.natCast_val, ZMod.cast_id]

end ExtCitation
