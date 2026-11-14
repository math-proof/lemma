import Def.ExtCitation_AdmissibleExtension
import Def.ExtCitation_KummerBridge

set_option autoImplicit false

universe u

namespace groupCohomology

variable {Γ : Type*} [Group Γ] {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable [DistribMulAction Γ V] [SMulCommClass Γ R V]


omit [SMulCommClass Γ R V] in

lemma extClassFun_mem (χ : Γ →* Rˣ) (v₀ : V) (C : Submodule R V)
    (hquot : ∀ σ : Γ, ∀ x : V, σ • x - (χ σ : R) • x ∈ C) (σ : Γ) :
    extClassFun χ v₀ σ ∈ C :=
  C.smul_mem _ (hquot σ v₀)

end groupCohomology

namespace ExtCitation

variable (p : ℕ) [Fact p.Prime]


lemma val_cycloChar (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ((cycloChar p σ : ZMod p) : ZMod p).val = cycloExp p σ := rfl

lemma coe_cycloChar (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ((cycloChar p σ : ZMod p)) = (cycloExp p σ : ZMod p) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [← val_cycloChar, ZMod.natCast_val, ZMod.cast_id]

end ExtCitation
