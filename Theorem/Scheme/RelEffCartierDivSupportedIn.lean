module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Theorem.Scheme.RelEffCartierDivFunctor

public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Scheme.RelEffCartierDiv

variable {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ}


public theorem supportedIn_iff {T : Scheme.{u}} {g : T ⟶ S} (D : RelEffCartierDiv f r g) (U : 𝒞.Opens) :
    D.SupportedIn U ↔ ∀ x ∈ D.I.support, pullback.fst f g x ∈ U :=
  Iff.rfl


public theorem SupportedIn.mono {T : Scheme.{u}} {g : T ⟶ S} {D : RelEffCartierDiv f r g} {U U' : 𝒞.Opens}
    (h : D.SupportedIn U) (hUU' : U ≤ U') : D.SupportedIn U' :=
  fun _ hx => hUU' (h hx)


@[simp] public theorem supportedIn_top {T : Scheme.{u}} {g : T ⟶ S} (D : RelEffCartierDiv f r g) :
    D.SupportedIn ⊤ :=
  fun _ _ => trivial


public theorem SupportedIn.pullbackAlong {T T' : Scheme.{u}} {g : T ⟶ S} {g' : T' ⟶ S}
    {D : RelEffCartierDiv f r g'} {U : 𝒞.Opens} (h : D.SupportedIn U) (φ : T ⟶ T')
    (hφ : φ ≫ g' = g) : (D.pullbackAlong φ hφ).SupportedIn U := by
  intro x hx
  change x ∈ (D.I.comap (mapOnProdOver f φ hφ)).support at hx
  rw [Scheme.IdealSheafData.support_comap] at hx
  have hx' : pullback.fst f g' (mapOnProdOver f φ hφ x) ∈ U := h hx
  rwa [← Scheme.Hom.comp_apply, mapOnProdOver_fst] at hx'

section Locus

variable {T : Scheme.{u}} {g : T ⟶ S}


public theorem mem_supportedInLocus_iff (D : RelEffCartierDiv f r g) (U : 𝒞.Opens) (t : T) :
    t ∈ D.supportedInLocus U ↔ ∀ z : ↥D.I.subscheme, (D.I.subschemeι ≫ pullback.snd f g) z = t →
      pullback.fst f g (D.I.subschemeι z) ∈ U :=
  Iff.rfl


public theorem supportedIn_pullbackAlong_iff (D : RelEffCartierDiv f r g) (U : 𝒞.Opens)
    {T' : Scheme.{u}} {g' : T' ⟶ S} (φ : T' ⟶ T) (hφ : φ ≫ g = g') :
    (D.pullbackAlong φ hφ).SupportedIn U ↔ Set.range φ ⊆ (D.supportedInLocus U : Set T) := by
  have hsupp : ((D.pullbackAlong φ hφ).I.support : Set ↥(pullback f g')) =
      mapOnProdOver f φ hφ ⁻¹' Set.range D.I.subschemeι := by
    rw [show (D.pullbackAlong φ hφ).I = D.I.comap (mapOnProdOver f φ hφ) from rfl,
      Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.range_subschemeι]
    rfl
  constructor
  · rintro h _ ⟨t', rfl⟩ z hz

    obtain ⟨w, hw₁, hw₂⟩ := Scheme.exists_preimage_of_isPullback
      (isPullback_mapOnProdOver f φ hφ) (D.I.subschemeι z) t'
      (by simpa [Scheme.Hom.comp_apply] using hz)
    have hw : w ∈ ((D.pullbackAlong φ hφ).I.support : Set _) := by
      rw [hsupp]; exact ⟨z, hw₁.symm⟩
    have := h hw
    change pullback.fst f g' w ∈ U at this
    rwa [← mapOnProdOver_fst f φ hφ, Scheme.Hom.comp_apply, hw₁] at this
  · intro h w hw
    rw [hsupp] at hw
    obtain ⟨z, hz⟩ := hw
    have ht : φ (pullback.snd f g' w) ∈ D.supportedInLocus U := h ⟨_, rfl⟩
    have := ht z (by
      rw [Scheme.Hom.comp_apply, hz, ← Scheme.Hom.comp_apply, mapOnProdOver_snd,
        Scheme.Hom.comp_apply])
    change pullback.fst f g' w ∈ U
    rwa [hz, ← Scheme.Hom.comp_apply, mapOnProdOver_fst] at this


public theorem supportedIn_iff_supportedInLocus_eq_top (D : RelEffCartierDiv f r g) (U : 𝒞.Opens) :
    D.SupportedIn U ↔ D.supportedInLocus U = ⊤ := by
  rw [← D.pullbackAlong_id, supportedIn_pullbackAlong_iff, D.pullbackAlong_id]
  constructor
  · intro h
    exact top_le_iff.mp fun t _ => h ⟨t, rfl⟩
  · rintro h - ⟨t, rfl⟩
    exact h.symm ▸ trivial

end Locus

variable (f r)


@[simp] public theorem mem_supportedIn_iff {U : 𝒞.Opens} {T : Scheme.{u}ᵒᵖ}
    (x : (RelEffCartierDiv.functor f r).obj T) :
    x ∈ (supportedIn f r U).obj T ↔ x.2.SupportedIn U :=
  Iff.rfl


public theorem supportedIn_mono {U U' : 𝒞.Opens} (h : U ≤ U') : supportedIn f r U ≤ supportedIn f r U' :=
  fun _ _ hx => SupportedIn.mono hx h


@[simp] public theorem supportedIn_top_eq : supportedIn f r (⊤ : 𝒞.Opens) = ⊤ :=
  top_le_iff.mp fun _ x _ => supportedIn_top x.2

end Scheme.RelEffCartierDiv
