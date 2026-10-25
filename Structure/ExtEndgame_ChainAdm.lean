import Mathlib
import Instance.GroupCohomology_SelmerAdm
import Def.DualSelmer_ExtConditions
import Def.ExtCitation_KummerBridge
import Structure.ExtCitation_AdmissibleExtension
import Def.Stickelberger_Basic
import Def.ExtEndgame_ChainAdm

set_option autoImplicit false

open CategoryTheory Module groupCohomology

namespace ExtCitation


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
