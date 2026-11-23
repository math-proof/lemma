module

public import Theorem.Scheme.RelEffCartierDiv

public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace RelEffCartierDiv

variable {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) (r : ℕ)

variable {f r} in

public theorem pullbackAlong_heq {T T' : Scheme.{u}} {g' : T' ⟶ S} (D : RelEffCartierDiv f r g')
    (φ : T ⟶ T') {g₁ g₂ : T ⟶ S} (h₁ : φ ≫ g' = g₁) (h₂ : φ ≫ g' = g₂) :
    HEq (D.pullbackAlong φ h₁) (D.pullbackAlong φ h₂) := by
  obtain rfl : g₁ = g₂ := h₁.symm.trans h₂
  rfl


@[simp] public theorem functor_map_fst {T T' : Scheme.{u}ᵒᵖ} (φ : T ⟶ T') (D : (RelEffCartierDiv.functor f r).obj T) :
    ((RelEffCartierDiv.functor f r).map φ D).1 = φ.unop ≫ D.1 := rfl


public theorem functor_map_snd {T T' : Scheme.{u}ᵒᵖ} (φ : T ⟶ T') (D : (RelEffCartierDiv.functor f r).obj T) :
    ((RelEffCartierDiv.functor f r).map φ D).2 = D.2.pullbackAlong φ.unop rfl := rfl


public theorem functor_map_apply {T T' : Scheme.{u}ᵒᵖ} (φ : T ⟶ T')
    (D : (RelEffCartierDiv.functor f r).obj T) :
    (RelEffCartierDiv.functor f r).map φ D = ⟨φ.unop ≫ D.1, D.2.pullbackAlong φ.unop rfl⟩ := rfl

variable {f r}


@[reassoc (attr := simp)]
public theorem IsUniversal.lift_comp (hU : Duniv.IsUniversal) {T : Scheme.{u}} {g : T ⟶ S}
    (D : RelEffCartierDiv f r g) : hU.lift D ≫ y = g :=
  (hU g D).exists.choose.2


public theorem IsUniversal.pullsBackOver_lift (hU : Duniv.IsUniversal) {T : Scheme.{u}} {g : T ⟶ S}
    (D : RelEffCartierDiv f r g) : PullsBackOver Duniv (hU.lift D) (hU.lift_comp D) D :=
  (hU g D).exists.choose_spec


public theorem IsUniversal.pullbackAlong_lift (hU : Duniv.IsUniversal) {T : Scheme.{u}} {g : T ⟶ S}
    (D : RelEffCartierDiv f r g) : Duniv.pullbackAlong (hU.lift D) (hU.lift_comp D) = D :=
  (PullsBackOver.eq_pullbackAlong (hU.pullsBackOver_lift D)).symm


public theorem IsUniversal.eq_lift (hU : Duniv.IsUniversal) {T : Scheme.{u}} {g : T ⟶ S}
    {D : RelEffCartierDiv f r g} {φ : T ⟶ Y} (hφ : φ ≫ y = g) (h : PullsBackOver Duniv φ hφ D) :
    φ = hU.lift D :=
  congrArg Subtype.val ((hU g D).unique (y₁ := ⟨φ, hφ⟩) h (hU.pullsBackOver_lift D))


@[simp] public theorem IsUniversal.lift_pullbackAlong (hU : Duniv.IsUniversal) {T : Scheme.{u}}
    (φ : T ⟶ Y) : hU.lift (Duniv.pullbackAlong φ rfl) = φ :=
  (hU.eq_lift rfl (pullsBackOver_pullbackAlong Duniv φ rfl)).symm


public theorem IsUniversal.hom_ext (hU : Duniv.IsUniversal) {T : Scheme.{u}} {φ ψ : T ⟶ Y}
    (hy : φ ≫ y = ψ ≫ y)
    (h : Duniv.I.comap (mapOnProdOver f φ rfl) = Duniv.I.comap (mapOnProdOver f ψ hy.symm)) :
    φ = ψ := by
  rw [← hU.lift_pullbackAlong φ]
  exact (hU.eq_lift (D := Duniv.pullbackAlong φ rfl) hy.symm h.symm).symm


public theorem IsUniversal.of_iso {Y'' : Scheme.{u}} {y'' : Y'' ⟶ S} (hU : Duniv.IsUniversal) (e : Y'' ≅ Y)
    (he : e.hom ≫ y = y'') : (Duniv.pullbackAlong e.hom he).IsUniversal := by
  intro T g D

  have key : ∀ (φ : T ⟶ Y'') (hφ : φ ≫ y'' = g),
      PullsBackOver (Duniv.pullbackAlong e.hom he) φ hφ D ↔
        PullsBackOver Duniv (φ ≫ e.hom) (by rw [Category.assoc, he, hφ]) D := by
    intro φ hφ
    change ((Duniv.pullbackAlong e.hom he).pullbackAlong φ hφ).I = D.I ↔
      (Duniv.pullbackAlong (φ ≫ e.hom) _).I = D.I
    rw [Duniv.pullbackAlong_comp]
  refine ⟨⟨hU.lift D ≫ e.inv, by rw [Category.assoc, ← he, e.inv_hom_id_assoc, hU.lift_comp]⟩,
    ?_, ?_⟩
  · change PullsBackOver _ (hU.lift D ≫ e.inv) _ D
    rw [key]
    change (Duniv.pullbackAlong ((hU.lift D ≫ e.inv) ≫ e.hom) _).I = D.I
    have h : (hU.lift D ≫ e.inv) ≫ e.hom = hU.lift D := by simp
    have hc : ∀ {φ₁ φ₂ : T ⟶ Y} (_ : φ₁ = φ₂) (h₁ : φ₁ ≫ y = g) (h₂ : φ₂ ≫ y = g),
        Duniv.pullbackAlong φ₁ h₁ = Duniv.pullbackAlong φ₂ h₂ := by
      rintro _ _ rfl _ _; rfl
    rw [hc h _ (hU.lift_comp D)]
    exact hU.pullsBackOver_lift D
  · rintro ⟨ψ, hψ⟩ hPB
    apply Subtype.ext
    change ψ = hU.lift D ≫ e.inv
    rw [← hU.eq_lift _ ((key ψ hψ).1 hPB), Category.assoc, e.hom_inv_id, Category.comp_id]


@[simp] public theorem IsUniversal.homEquiv_apply (hU : Duniv.IsUniversal) {T : Scheme.{u}} (φ : T ⟶ Y) :
    hU.homEquiv T φ = ⟨φ ≫ y, Duniv.pullbackAlong φ rfl⟩ := rfl


@[simp] public theorem IsUniversal.homEquiv_symm_apply (hU : Duniv.IsUniversal) {T : Scheme.{u}}
    (D : Σ g : T ⟶ S, RelEffCartierDiv f r g) : (hU.homEquiv T).symm D = hU.lift D.2 := rfl


public theorem IsUniversal.representableBy_homEquiv_apply (hU : Duniv.IsUniversal) {T : Scheme.{u}}
    (φ : T ⟶ Y) :
    hU.representableBy.homEquiv φ = ⟨φ ≫ y, Duniv.pullbackAlong φ rfl⟩ := rfl


public theorem isUniversal_of_representableBy (e : (RelEffCartierDiv.functor f r).RepresentableBy Y) :
    (e.homEquiv (𝟙 Y)).2.IsUniversal := by
  intro T g D
  have key : ∀ φ : T ⟶ Y, e.homEquiv φ =
      ⟨φ ≫ (e.homEquiv (𝟙 Y)).1, (e.homEquiv (𝟙 Y)).2.pullbackAlong φ rfl⟩ := fun φ => by
    have h := e.homEquiv_comp φ (𝟙 Y)
    rw [Category.comp_id] at h
    exact h
  have H : (⟨e.homEquiv.symm ⟨g, D⟩ ≫ (e.homEquiv (𝟙 Y)).1,
      (e.homEquiv (𝟙 Y)).2.pullbackAlong (e.homEquiv.symm ⟨g, D⟩) rfl⟩ :
        Σ g : T ⟶ S, RelEffCartierDiv f r g) = ⟨g, D⟩ :=
    (key _).symm.trans (e.homEquiv.apply_symm_apply _)
  have h1 : e.homEquiv.symm ⟨g, D⟩ ≫ (e.homEquiv (𝟙 Y)).1 = g := congrArg Sigma.fst H
  refine ⟨⟨e.homEquiv.symm ⟨g, D⟩, h1⟩, ?_, ?_⟩
  · have h3 : (e.homEquiv (𝟙 Y)).2.pullbackAlong (e.homEquiv.symm ⟨g, D⟩) h1 = D :=
      eq_of_heq (((e.homEquiv (𝟙 Y)).2.pullbackAlong_heq _ h1 rfl).trans (Sigma.ext_iff.1 H).2)
    exact congrArg RelEffCartierDiv.I h3
  · rintro ⟨ψ, hψ⟩ hPB
    apply Subtype.ext
    apply e.homEquiv.injective
    rw [Equiv.apply_symm_apply, key ψ]
    exact Sigma.ext hψ (((e.homEquiv (𝟙 Y)).2.pullbackAlong_heq ψ rfl hψ).trans
      (heq_of_eq (PullsBackOver.eq_pullbackAlong hPB).symm))

variable (f r) in


public theorem isRepresentable_functor_iff :
    (RelEffCartierDiv.functor f r).IsRepresentable ↔
      ∃ (Y : Scheme.{u}) (y : Y ⟶ S) (Duniv : RelEffCartierDiv f r y), Duniv.IsUniversal := by
  constructor
  · rintro ⟨Y, ⟨e⟩⟩
    exact ⟨Y, _, _, isUniversal_of_representableBy e⟩
  · rintro ⟨Y, y, Duniv, hU⟩
    exact ⟨Y, ⟨hU.representableBy⟩⟩

end Representability

end RelEffCartierDiv

end AlgebraicGeometry
