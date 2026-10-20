import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

private lemma eq_of_isStandardSmoothOfRelativeDimension {R S : Type u} [CommRing R] [CommRing S]
    [Nontrivial S] {m n : ℕ} (f : R →+* S) (hm : f.IsStandardSmoothOfRelativeDimension m)
    (hn : f.IsStandardSmoothOfRelativeDimension n) : m = n := by
  algebraize [f]
  have h₁ := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
    (R := R) (S := S) m
  have h₂ := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
    (R := R) (S := S) n
  exact_mod_cast h₁.symm.trans h₂
private lemma nontrivial_localization_away {S : Type u} [CommRing S] {t : S} (ht : ¬IsNilpotent t) :
    Nontrivial (Localization.Away t) := by
  refine not_subsingleton_iff_nontrivial.mp fun hsub => ht ?_
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp
    ((IsLocalization.subsingleton_iff (M := Submonoid.powers t) (S := Localization.Away t)).mp
      hsub)
  exact ⟨k, hk⟩
private lemma exists_not_isNilpotent {S : Type u} [CommRing S] [Nontrivial S] {s : Set S}
    (hs : Ideal.span s = ⊤) : ∃ t ∈ s, ¬IsNilpotent t := by
  by_contra hall
  simp only [not_exists, not_and, not_not] at hall
  have hle : Ideal.span s ≤ nilradical S := Ideal.span_le.mpr fun t ht => mem_nilradical.mpr (hall t ht)
  rw [hs, top_le_iff] at hle
  obtain ⟨k, hk⟩ := mem_nilradical.mp (hle ▸ Submodule.mem_top : (1 : S) ∈ nilradical S)
  exact one_ne_zero ((one_pow k).symm.trans hk)
/--
[AlgebraicGeometry_smoothOfRelativeDimension_of_irreducibleSpace](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_smoothOfRelativeDimension_of_irreducibleSpace.lean)
-/
@[path]
private lemma main (n : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace X] [Smooth f]
    (V : X.Opens) (hV : (V : Set X).Nonempty) [SmoothOfRelativeDimension n (V.ι ≫ f)] :
    SmoothOfRelativeDimension n f := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U₁, hU₁, V₁, hV₁, hxV₁, e₁, hA⟩ := Smooth.exists_isStandardSmooth f x
  obtain ⟨m, hm⟩ : ∃ m, (f.appLE U₁ V₁ e₁).hom.IsStandardSmoothOfRelativeDimension m := by
    algebraize [(f.appLE U₁ V₁ e₁).hom]
    obtain ⟨_, _, _, _, ⟨P⟩⟩ := hA
    exact ⟨_, _, _, _, ‹_›, P, rfl⟩
  obtain ⟨w, hwV₁, hwV⟩ := nonempty_preirreducible_inter V₁.isOpen V.isOpen ⟨x, hxV₁⟩ hV
  obtain ⟨a, haV, hwa⟩ := hV₁.exists_basicOpen_le ⟨w, hwV⟩ hwV₁
  have hV₂ : IsAffineOpen (X.basicOpen a) := hV₁.basicOpen a
  have e₂ : X.basicOpen a ≤ f ⁻¹ᵁ U₁ := (X.basicOpen_le a).trans e₁
  let _ : Nonempty ↥(X.basicOpen a) := ⟨⟨w, hwa⟩⟩
  let _ := hV₁.isLocalization_basicOpen a
  have hm₂ : (f.appLE U₁ (X.basicOpen a) e₂).hom.IsStandardSmoothOfRelativeDimension (0 + m) := by
    have heq : (f.appLE U₁ (X.basicOpen a) e₂).hom =
        (algebraMap Γ(X, V₁) Γ(X, X.basicOpen a)).comp (f.appLE U₁ V₁ e₁).hom := by
      change _ = (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom.comp (f.appLE U₁ V₁ e₁).hom
      rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_map]
    rw [heq]
    exact (RingHom.IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway a).comp hm
  have hn₂ : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)
      (f.appLE U₁ (X.basicOpen a) e₂).hom := by
    have hle : X.basicOpen a ≤ V.ι.opensRange := by rwa [Scheme.Opens.opensRange_ι]
    have haff : IsAffineOpen (V.ι ⁻¹ᵁ X.basicOpen a) := hV₂.preimage_of_isOpenImmersion V.ι hle
    have e₃ : V.ι ⁻¹ᵁ X.basicOpen a ≤ (V.ι ≫ f) ⁻¹ᵁ U₁ := by
      rw [Scheme.Hom.comp_preimage]
      exact fun v hv => e₂ hv
    have HL := HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension n) (V.ι ≫ f)
      inferInstance ⟨U₁, hU₁⟩ ⟨_, haff⟩ e₃
    have key : (V.ι ≫ f).appLE U₁ (V.ι ⁻¹ᵁ X.basicOpen a) e₃ =
        f.appLE U₁ (X.basicOpen a) e₂ ≫ V.ι.app (X.basicOpen a) := by
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    rw [key] at HL
    let _ := V.ι.isIso_app (X.basicOpen a) hle
    exact (RingHom.RespectsIso.cancel_right_isIso (RingHom.locally_respectsIso
      RingHom.isStandardSmoothOfRelativeDimension_respectsIso) _ _).mp HL
  obtain ⟨s, hs, hQ⟩ := hn₂
  obtain ⟨t, hts, ht⟩ := exists_not_isNilpotent hs
  let _ := nontrivial_localization_away ht
  have hψn := hQ t hts
  have hψm := (RingHom.IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway
    (Rᵣ := Localization.Away t) t).comp hm₂
  have hmn : m = n := by
    simpa using eq_of_isStandardSmoothOfRelativeDimension _ hψm hψn
  exact ⟨U₁, hU₁, V₁, hV₁, hxV₁, e₁, hmn ▸ hm⟩

-- created on 2026-10-20
