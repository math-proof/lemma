import Mathlib.CategoryTheory.Subfunctor.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Lemma.Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RelEffCartierDiv

variable {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ}

def SupportedIn {T : Scheme.{u}} {g : T ⟶ S} (D : RelEffCartierDiv f r g) (U : 𝒞.Opens) : Prop :=
  (D.I.support : Set ↥(pullback f g)) ⊆ ((pullback.fst f g) ⁻¹ᵁ U : (pullback f g).Opens)

lemma supportedIn_iff {T : Scheme.{u}} {g : T ⟶ S} (D : RelEffCartierDiv f r g) (U : 𝒞.Opens) :
    D.SupportedIn U ↔ ∀ x ∈ D.I.support, pullback.fst f g x ∈ U :=
  Iff.rfl

lemma SupportedIn.mono {T : Scheme.{u}} {g : T ⟶ S} {D : RelEffCartierDiv f r g} {U U' : 𝒞.Opens}
    (h : D.SupportedIn U) (hUU' : U ≤ U') : D.SupportedIn U' :=
  fun _ hx => hUU' (h hx)

@[simp] lemma supportedIn_top {T : Scheme.{u}} {g : T ⟶ S} (D : RelEffCartierDiv f r g) :
    D.SupportedIn ⊤ :=
  fun _ _ => trivial

lemma SupportedIn.pullbackAlong {T T' : Scheme.{u}} {g : T ⟶ S} {g' : T' ⟶ S}
    {D : RelEffCartierDiv f r g'} {U : 𝒞.Opens} (h : D.SupportedIn U) (φ : T ⟶ T')
    (hφ : φ ≫ g' = g) : (D.pullbackAlong φ hφ).SupportedIn U := by
  intro x hx
  change x ∈ (D.I.comap (mapOnProdOver f φ hφ)).support at hx
  rw [Scheme.IdealSheafData.support_comap] at hx
  have hx' : pullback.fst f g' (mapOnProdOver f φ hφ x) ∈ U := h hx
  rwa [← Scheme.Hom.comp_apply, mapOnProdOver_fst] at hx'

section Locus

variable {T : Scheme.{u}} {g : T ⟶ S}

def supportedInLocus (D : RelEffCartierDiv f r g) (U : 𝒞.Opens) : T.Opens where
  carrier := {t | ∀ z : ↥D.I.subscheme, (D.I.subschemeι ≫ pullback.snd f g) z = t →
    pullback.fst f g (D.I.subschemeι z) ∈ U}
  is_open' := by
    have := D.isFinite
    have hcl : IsClosed ((D.I.subschemeι ≫ pullback.snd f g) ''
        ((D.I.subschemeι ≫ pullback.fst f g) ⁻¹ᵁ U : Set ↥D.I.subscheme)ᶜ) :=
      (D.I.subschemeι ≫ pullback.snd f g).isClosedMap _
        ((D.I.subschemeι ≫ pullback.fst f g) ⁻¹ᵁ U).2.isClosed_compl
    convert hcl.isOpen_compl using 1
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_image, not_exists, not_and]
    exact ⟨fun h z hz hzt => hz (by simpa [Scheme.Hom.comp_apply] using h z hzt),
      fun h z hzt => by
        by_contra hz
        exact h z (by simpa [Scheme.Hom.comp_apply] using hz) hzt⟩

lemma mem_supportedInLocus_iff (D : RelEffCartierDiv f r g) (U : 𝒞.Opens) (t : T) :
    t ∈ D.supportedInLocus U ↔ ∀ z : ↥D.I.subscheme, (D.I.subschemeι ≫ pullback.snd f g) z = t →
      pullback.fst f g (D.I.subschemeι z) ∈ U :=
  Iff.rfl

lemma supportedIn_pullbackAlong_iff (D : RelEffCartierDiv f r g) (U : 𝒞.Opens)
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

lemma supportedIn_iff_supportedInLocus_eq_top (D : RelEffCartierDiv f r g) (U : 𝒞.Opens) :
    D.SupportedIn U ↔ D.supportedInLocus U = ⊤ := by
  rw [← D.pullbackAlong_id, supportedIn_pullbackAlong_iff, D.pullbackAlong_id]
  constructor
  · intro h
    exact top_le_iff.mp fun t _ => h ⟨t, rfl⟩
  · rintro h - ⟨t, rfl⟩
    exact h.symm ▸ trivial

end Locus

variable (f r)

def supportedIn (U : 𝒞.Opens) : Subfunctor (RelEffCartierDiv.functor f r) where
  obj T := {x | x.2.SupportedIn U}
  map {T T'} φ := by
    rintro ⟨g, D⟩ (hD : D.SupportedIn U)
    exact hD.pullbackAlong φ.unop rfl

variable {f r}

@[simp] lemma mem_supportedIn_iff {U : 𝒞.Opens} {T : Scheme.{u}ᵒᵖ}
    (x : (RelEffCartierDiv.functor f r).obj T) :
    x ∈ (supportedIn f r U).obj T ↔ x.2.SupportedIn U :=
  Iff.rfl

lemma supportedIn_mono {U U' : 𝒞.Opens} (h : U ≤ U') : supportedIn f r U ≤ supportedIn f r U' :=
  fun _ _ hx => SupportedIn.mono hx h

@[simp] lemma supportedIn_top_eq : supportedIn f r (⊤ : 𝒞.Opens) = ⊤ :=
  top_le_iff.mp fun _ x _ => supportedIn_top x.2

end AlgebraicGeometry.RelEffCartierDiv
