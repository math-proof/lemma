module

public import Mathlib
public import Def.GroupCohomology_SelmerAdm
public import Abbrev.DualSelmer_ExtConditions
public import Def.DualSelmer_ExtConditions
public import Def.ExtCitation_KummerBridge
public import Def.ExtCitation_AdmissibleExtension
public import Def.Stickelberger_Basic

@[expose] public section

set_option autoImplicit false

open CategoryTheory Module groupCohomology

namespace ExtCitation

def ExtClassesAreCoboundaries (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V]
    [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ZMod p) V]
    (C : Submodule (ZMod p) V), IsAdmissibleExtension p V C →
    ∀ v₀ : V, v₀ ∉ C →
      ∃ b ∈ C, ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        extClassFun (cycloChar p) v₀ σ
          = ((((cycloChar p σ)⁻¹ : (ZMod p)ˣ) : ZMod p)) • b - b

def ExtSelmerRealization (p : ℕ) [Fact p.Prime]
    {Γ' : Type} [Group Γ'] {ι' : Type} [Fintype ι'] {Γv' : ι' → Type} [∀ v, Group (Γv' v)]
    (loc' : ∀ v, Γv' v →* Γ') (ψ : Γ' →* (ZMod p)ˣ) (P : Set ι')
    (U : ∀ v, Submodule (ZMod p) (H1 (Rep.res (loc' v) (ofChar (k := ZMod p) ψ)))) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V]
    [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ZMod p) V]
    (C : Submodule (ZMod p) V), IsAdmissibleExtension p V C →
    ∀ v₀ : V, v₀ ∉ C →
      ∃ x ∈ selmer loc' (ofChar (k := ZMod p) ψ)
          (extConditions loc' (ofChar (k := ZMod p) ψ) P U),
        (x = 0 →
          ∃ b ∈ C, ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
            extClassFun (cycloChar p) v₀ σ
              = ((((cycloChar p σ)⁻¹ : (ZMod p)ˣ) : ZMod p)) • b - b)

def ExtSelmerRealizationAdm (p : ℕ) [Fact p.Prime]
    {Γ' : Type} [Group Γ'] {ι' : Type} [Fintype ι'] {Γv' : ι' → Type} [∀ v, Group (Γv' v)]
    (loc' : ∀ v, Γv' v →* Γ') (ψ : Γ' →* (ZMod p)ˣ) (P : Set ι')
    (U : ∀ v, Submodule (ZMod p) (H1 (Rep.res (loc' v) (ofChar (k := ZMod p) ψ))))
    (adm : Submodule (ZMod p) (H1 (ofChar (k := ZMod p) ψ))) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V]
    [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ZMod p) V]
    (C : Submodule (ZMod p) V), IsAdmissibleExtension p V C →
    ∀ v₀ : V, v₀ ∉ C →
      ∃ x ∈ selmerAdm loc' (ofChar (k := ZMod p) ψ)
          (extConditions loc' (ofChar (k := ZMod p) ψ) P U) adm,
        (x = 0 →
          ∃ b ∈ C, ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
            extClassFun (cycloChar p) v₀ σ
              = ((((cycloChar p σ)⁻¹ : (ZMod p)ˣ) : ZMod p)) • b - b)

end ExtCitation
