import Mathlib
import Lemma.Definitions.Def_GroupCohomology_SelmerAdm
import Lemma.Definitions.Def_DualSelmer_ExtConditions
import Lemma.Definitions.Def_ExtCitation_KummerBridge
import Lemma.Definitions.Def_ExtCitation_AdmissibleExtension
import Lemma.Definitions.Def_Stickelberger_Basic

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

theorem extSelmerRealizationAdm_top_iff (p : ℕ) [Fact p.Prime]
    {Γ' : Type} [Group Γ'] {ι' : Type} [Fintype ι'] {Γv' : ι' → Type} [∀ v, Group (Γv' v)]
    (loc' : ∀ v, Γv' v →* Γ') (ψ : Γ' →* (ZMod p)ˣ) (P : Set ι')
    (U : ∀ v, Submodule (ZMod p) (H1 (Rep.res (loc' v) (ofChar (k := ZMod p) ψ)))) :
    ExtSelmerRealizationAdm p loc' ψ P U ⊤ ↔ ExtSelmerRealization p loc' ψ P U := by
  unfold ExtSelmerRealizationAdm ExtSelmerRealization
  simp_rw [selmerAdm_top]

structure ExtChainAdmResidual (p : ℕ) [Fact p.Prime]
    {Γ' : Type} [Group Γ'] {ι' : Type} [Fintype ι'] {Γv' : ι' → Type} [∀ v, Group (Γv' v)]
    (loc' : ∀ v, Γv' v →* Γ') (ψ : Γ' →* (ZMod p)ˣ) (M' : Rep (ZMod p) Γ')
    (pairing : ∀ v, H1 (Rep.res (loc' v) (ofChar (k := ZMod p) ψ)) →ₗ[ZMod p]
      H1 (Rep.res (loc' v) M') →ₗ[ZMod p] (ZMod p))
    (P : Set ι')
    (U : ∀ v, Submodule (ZMod p) (H1 (Rep.res (loc' v) (ofChar (k := ZMod p) ψ))))
    (adm : Submodule (ZMod p) (H1 (ofChar (k := ZMod p) ψ)))
    (adm' : Submodule (ZMod p) (H1 M'))
    {A : Type} [AddCommGroup A] [Module (ZMod p) A]
    (ρ : (ZMod p)ˣ →* Module.End (ZMod p) A)
    (f : H1 M' →ₗ[ZMod p] A) : Prop where

  hrealAdm : ExtSelmerRealizationAdm p loc' ψ P U adm

  hGWAdm : IsGreenbergWilesLeDatumAdm loc' (ofChar (k := ZMod p) ψ) M' pairing
    (extConditions loc' (ofChar (k := ZMod p) ψ) P U) adm adm'

  hsum : ∑ v, finrank (ZMod p) (extConditions loc' (ofChar (k := ZMod p) ψ) P U v)
    ≤ ∑ v, finrank (ZMod p) (Rep.res (loc' v) (ofChar (k := ZMod p) ψ)).ρ.invariants

  hM : finrank (ZMod p) (ofChar (k := ZMod p) ψ).ρ.invariants = 0

  hM' : finrank (ZMod p) M'.ρ.invariants = 0

  heig : ∀ x ∈ selmerAdm loc' M' (dualConditions loc' (ofChar (k := ZMod p) ψ) M' pairing
      (extConditions loc' (ofChar (k := ZMod p) ψ) P U)) adm',
    Stickelberger.IsOmegaEigenvector ρ (p - 2) (f x)

  hinj : ∀ x ∈ selmerAdm loc' M' (dualConditions loc' (ofChar (k := ZMod p) ψ) M' pairing
      (extConditions loc' (ofChar (k := ZMod p) ψ) P U)) adm',
    f x = 0 → x = 0

  hann : Stickelberger.StickelbergerAnnihilates ρ

end ExtCitation
