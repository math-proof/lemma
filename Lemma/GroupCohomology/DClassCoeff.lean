import Def.CohCarrier_Level
import Lemma.GroupCohomology.TransferHecke

set_option autoImplicit false

namespace HeckeCohomology

open CategoryTheory groupCohomology

open scoped MatrixGroups

section DClass

variable {k : Type} [CommRing k] (M : ℕ) (H : Subgroup (ZMod M)ˣ)

def unitsOf : ↥(CohCarrier.GammaH M H) →* (ZMod M)ˣ :=
  (CohCarrier.gamma0Units M).comp (Subgroup.inclusion (CohCarrier.GammaH_le_Gamma0 H))

theorem val_unitsOf (γ : ↥(CohCarrier.GammaH M H)) :
    (unitsOf M H γ : ZMod M) = (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) := rfl

variable (ℓ : ℕ)

theorem unitsOf_conjL (s : ↥(CohCarrier.GammaHUpper M H ℓ)) :
    unitsOf M H (CohCarrier.conjL M H ℓ s) = unitsOf M H (s : ↥(CohCarrier.GammaH M H)) := by
  apply Units.ext
  rw [val_unitsOf, val_unitsOf]
  show (((CohCarrier.conjUpperMat ℓ ((s : ↥(CohCarrier.GammaH M H)) : SL(2, ℤ))
      (CohCarrier.dvd_of_mem_GammaHUpper M H ℓ s)) 1 1 : ℤ) : ZMod M) =
    ((((s : ↥(CohCarrier.GammaH M H)) : SL(2, ℤ)) 1 1 : ℤ) : ZMod M)
  rw [CohCarrier.conjUpperMat_apply_11]

noncomputable def cTop : ↥(CohCarrier.GammaHUpper M H ℓ) →* ↥(⊤ : Subgroup ↥(CohCarrier.GammaH M H)) :=
  (CohCarrier.conjL M H ℓ).codRestrict ⊤ fun _ => Subgroup.mem_top _

theorem subtype_comp_cTop :
    (⊤ : Subgroup ↥(CohCarrier.GammaH M H)).subtype.comp (cTop M H ℓ) =
      CohCarrier.conjL M H ℓ :=
  MonoidHom.ext fun _ => rfl

theorem isTwist_id_of_comp_eq {Γ : Type} [Group Γ] (S₁ S₂ : Subgroup Γ) (c : S₂ →* S₁)
    (A : Rep k Γ) (h : ∀ s : S₂, A.ρ ((c s : S₁) : Γ) = A.ρ (s : Γ)) :
    IsTwist S₁ S₂ c A LinearMap.id := fun s a => by
  rw [LinearMap.id_apply, LinearMap.id_apply, h]

def IsDClass (A : Rep k ↥(CohCarrier.GammaH M H)) : Prop :=
  ∃ θ : Representation k (ZMod M)ˣ A, ∀ γ, A.ρ γ = θ (unitsOf M H γ)

noncomputable def dTwist {V : Type} [AddCommGroup V] [Module k V]
    (θ : Representation k (ZMod M)ˣ V) : Rep k ↥(CohCarrier.GammaH M H) :=
  Rep.of (θ.comp (unitsOf M H))

theorem dTwist_ρ {V : Type} [AddCommGroup V] [Module k V] (θ : Representation k (ZMod M)ˣ V)
    (γ : ↥(CohCarrier.GammaH M H)) : (dTwist M H θ).ρ γ = θ (unitsOf M H γ) := rfl

theorem isDClass_dTwist {V : Type} [AddCommGroup V] [Module k V]
    (θ : Representation k (ZMod M)ˣ V) : IsDClass M H (dTwist M H θ) := ⟨θ, fun _ => rfl⟩

theorem ρ_cTop_eq (A : Rep k ↥(CohCarrier.GammaH M H)) (hA : IsDClass M H A)
    (s : ↥(CohCarrier.GammaHUpper M H ℓ)) :
    A.ρ ((cTop M H ℓ s : (⊤ : Subgroup ↥(CohCarrier.GammaH M H))) : ↥(CohCarrier.GammaH M H)) =
      A.ρ (s : ↥(CohCarrier.GammaH M H)) := by
  obtain ⟨θ, hθ⟩ := hA
  rw [hθ, hθ]
  show θ (unitsOf M H (CohCarrier.conjL M H ℓ s)) = θ (unitsOf M H s)
  rw [unitsOf_conjL]

theorem isTwist_id_of_isDClass (A : Rep k ↥(CohCarrier.GammaH M H)) (hA : IsDClass M H A) :
    IsTwist ⊤ (CohCarrier.GammaHUpper M H ℓ) (cTop M H ℓ) A LinearMap.id :=
  isTwist_id_of_comp_eq ⊤ _ (cTop M H ℓ) A (ρ_cTop_eq M H ℓ A hA)

variable [NeZero ℓ]

noncomputable def heckeH1D (A : Rep k ↥(CohCarrier.GammaH M H)) (hA : IsDClass M H A) :
    H1 A →ₗ[k] H1 A :=
  heckeH1 ⊤ (CohCarrier.GammaHUpper M H ℓ) (cTop M H ℓ) A LinearMap.id
    (isTwist_id_of_isDClass M H ℓ A hA)

noncomputable def heckeInvD (A : Rep k ↥(CohCarrier.GammaH M H)) (hA : IsDClass M H A) :
    A.ρ.invariants →ₗ[k] A.ρ.invariants :=
  heckeInv ⊤ (CohCarrier.GammaHUpper M H ℓ) (cTop M H ℓ) A LinearMap.id
    (isTwist_id_of_isDClass M H ℓ A hA)

end DClass

section UnitsCharacter

variable {Λ : Type} [CommRing Λ] (M : ℕ) (H : Subgroup (ZMod M)ˣ) (χ : (ZMod M)ˣ →* Λˣ)

def unitRep (N : Type) [AddCommGroup N] [Module Λ N] : Representation Λ (ZMod M)ˣ N :=
  (Module.toModuleEnd Λ N).toMonoidHom.comp ((Units.coeHom Λ).comp χ)

theorem unitRep_apply (N : Type) [AddCommGroup N] [Module Λ N] (u : (ZMod M)ˣ) (n : N) :
    unitRep M χ N u n = ((χ u : Λˣ) : Λ) • n := rfl

noncomputable def dMod (N : Type) [AddCommGroup N] [Module Λ N] :
    Rep Λ ↥(CohCarrier.GammaH M H) :=
  dTwist M H (unitRep M χ N)

theorem isDClass_dMod (N : Type) [AddCommGroup N] [Module Λ N] :
    IsDClass M H (dMod M H χ N) :=
  isDClass_dTwist M H _

noncomputable def dMap {N N' : Type} [AddCommGroup N] [Module Λ N] [AddCommGroup N']
    [Module Λ N'] (f : N →ₗ[Λ] N') : dMod M H χ N ⟶ dMod M H χ N' :=
  Rep.ofHom ⟨f, fun g => by
    ext n
    show f (((χ (unitsOf M H g) : Λˣ) : Λ) • n) = ((χ (unitsOf M H g) : Λˣ) : Λ) • f n
    rw [map_smul]⟩

noncomputable def dSES {N₁ N₂ N₃ : Type} [AddCommGroup N₁] [Module Λ N₁] [AddCommGroup N₂]
    [Module Λ N₂] [AddCommGroup N₃] [Module Λ N₃] (f : N₁ →ₗ[Λ] N₂) (g : N₂ →ₗ[Λ] N₃)
    (hfg : ∀ x, g (f x) = 0) : ShortComplex (Rep Λ ↥(CohCarrier.GammaH M H)) where
  X₁ := dMod M H χ N₁
  X₂ := dMod M H χ N₂
  X₃ := dMod M H χ N₃
  f := dMap M H χ f
  g := dMap M H χ g
  zero := by ext x; exact hfg x

noncomputable def idealSES (I : Ideal Λ) : ShortComplex (Rep Λ ↥(CohCarrier.GammaH M H)) :=
  dSES M H χ I.subtype I.mkQ fun x => (Submodule.Quotient.mk_eq_zero I).2 x.2

end UnitsCharacter

end HeckeCohomology
