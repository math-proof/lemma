import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_Scheme_Modules_locallyIso_of_locallyIso_pullback_pi_localizationAway](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_locallyIso_of_locallyIso_pullback_pi_localizationAway.lean)
-/
@[path]
private lemma main
  {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    {X X₁ : (Scheme : Type (u + 1))} (f : X ⟶ Spec (CommRingCat.of S))
    (f₁ : X₁ ⟶ Spec (CommRingCat.of (∀ i : Fin k, Localization.Away (r i))))
    (c : X₁ ⟶ X) (hc : IsPullback c f₁ f (Spec.map (CommRingCat.ofHom (algebraMap S (∀ i : Fin k, Localization.Away (r i))))))
    (L M : X.Modules)
    (h : ∀ s₁ : ↥(Spec (CommRingCat.of (∀ i : Fin k, Localization.Away (r i)))), ∃ U₁ : (Spec (CommRingCat.of (∀ i : Fin k, Localization.Away (r i)))).Opens, s₁ ∈ U₁ ∧ Nonempty ((Scheme.Modules.pullback ((Scheme.Opens.ι ((TopologicalSpace.Opens.map f₁.base).obj U₁)))).obj ((Scheme.Modules.pullback c).obj L) ≅ (Scheme.Modules.pullback ((Scheme.Opens.ι ((TopologicalSpace.Opens.map f₁.base).obj U₁)))).obj ((Scheme.Modules.pullback c).obj M))) :
    ∀ s : ↥(Spec (CommRingCat.of S)), ∃ U : (Spec (CommRingCat.of S)).Opens, s ∈ U ∧ Nonempty ((Scheme.Modules.pullback ((Scheme.Opens.ι ((TopologicalSpace.Opens.map f.base).obj U)))).obj L ≅ (Scheme.Modules.pullback ((Scheme.Opens.ι ((TopologicalSpace.Opens.map f.base).obj U)))).obj M) := by
  classical
  intro s
  obtain ⟨i, hi⟩ : ∃ i, r i ∉ s.asIdeal := by
    by_contra hall
    push Not at hall
    have hle : Ideal.span (Set.range r) ≤ s.asIdeal := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      apply hall i
    rw [hr, top_le_iff] at hle
    apply s.isPrime.ne_top hle
  let Sᵢ := Localization.Away (r i)
  let ℓ := Spec.map (CommRingCat.ofHom (algebraMap S Sᵢ))
  let j := Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun i : Fin k => Localization.Away (r i)) i))
  let π := Spec.map (CommRingCat.ofHom (algebraMap S (∀ i : Fin k, Localization.Away (r i))))
  have hjπ : j ≫ π = ℓ := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    apply congrArg (fun φ => Spec.map (CommRingCat.ofHom φ)) (RingHom.ext fun x => rfl)
  let _ : IsOpenImmersion ℓ := inferInstance
  obtain ⟨s', hs'⟩ : s ∈ Set.range ℓ.base := by
    change s ∈ Set.range (PrimeSpectrum.comap (algebraMap S Sᵢ))
    rwa [PrimeSpectrum.localization_away_comap_range Sᵢ (r i)]
  obtain ⟨U₁, hs₁, ⟨Φ⟩⟩ := h (j.base s')
  let W : (Spec (CommRingCat.of Sᵢ)).Opens := ((TopologicalSpace.Opens.map j.base).obj U₁)
  let U : (Spec (CommRingCat.of S)).Opens := (Scheme.Hom.opensFunctor ℓ).obj W
  have hsU : s ∈ U := ⟨s', hs₁, hs'⟩
  refine ⟨U, hsU, ?_⟩
  have hrange : Set.range (((Scheme.Opens.ι ((TopologicalSpace.Opens.map f.base).obj U)) ≫ f).base) ⊆ Set.range ℓ.base := by
    rintro _ ⟨x, rfl⟩
    have hx : f.base x.1 ∈ U := x.2
    obtain ⟨y, -, hy⟩ := hx
    refine ⟨y, ?_⟩
    show ℓ.base y = f.base (((Scheme.Opens.ι ((TopologicalSpace.Opens.map f.base).obj U))).base x)
    apply hy
  let m := IsOpenImmersion.lift ℓ (((Scheme.Opens.ι ((TopologicalSpace.Opens.map f.base).obj U)) ≫ f)) hrange
  have hm : m ≫ ℓ = (Scheme.Opens.ι ((TopologicalSpace.Opens.map f.base).obj U)) ≫ f := IsOpenImmersion.lift_fac _ _ _
  have w : (Scheme.Opens.ι ((TopologicalSpace.Opens.map f.base).obj U)) ≫ f = (m ≫ j) ≫ π := by rw [Category.assoc, hjπ, hm]
  let ρ₀ := hc.lift (Scheme.Opens.ι ((TopologicalSpace.Opens.map f.base).obj U)) (m ≫ j) w
  have hρ₀c : ρ₀ ≫ c = (Scheme.Opens.ι ((TopologicalSpace.Opens.map f.base).obj U)) := hc.lift_fst _ _ _
  have hρ₀f : ρ₀ ≫ f₁ = m ≫ j := hc.lift_snd _ _ _
  have hmem : ∀ x, ρ₀.base x ∈ ((TopologicalSpace.Opens.map f₁.base).obj U₁) := by
    intro x
    show f₁.base (ρ₀.base x) ∈ U₁
    have e1 : (ρ₀ ≫ f₁).base x = (m ≫ j).base x := by rw [hρ₀f]
    change f₁.base (ρ₀.base x) = j.base (m.base x) at e1
    rw [e1]
    have h1 : ℓ.base (m.base x) ∈ (Scheme.Hom.opensFunctor ℓ).obj W := by
      have e2 : (m ≫ ℓ).base x = (((Scheme.Opens.ι ((TopologicalSpace.Opens.map f.base).obj U)) ≫ f).base x) := by rw [hm]
      change ℓ.base (m.base x) = f.base (((Scheme.Opens.ι ((TopologicalSpace.Opens.map f.base).obj U))).base x) at e2
      rw [e2]
      apply x.2
    have h2 : m.base x ∈ ((TopologicalSpace.Opens.map ℓ.base).obj ((Scheme.Hom.opensFunctor ℓ).obj W)) := h1
    rwa [Scheme.Hom.preimage_image_eq] at h2
  have hrange₁ : Set.range ρ₀.base ⊆ Set.range ((Scheme.Opens.ι ((TopologicalSpace.Opens.map f₁.base).obj U₁))).base := by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨ρ₀.base x, hmem x⟩, rfl⟩
  let ρ := IsOpenImmersion.lift (Scheme.Opens.ι ((TopologicalSpace.Opens.map f₁.base).obj U₁)) ρ₀ hrange₁
  have hρ : ρ ≫ (Scheme.Opens.ι ((TopologicalSpace.Opens.map f₁.base).obj U₁)) = ρ₀ := IsOpenImmersion.lift_fac _ _ _
  have key : (Scheme.Opens.ι ((TopologicalSpace.Opens.map f.base).obj U)) = ρ ≫ (Scheme.Opens.ι ((TopologicalSpace.Opens.map f₁.base).obj U₁)) ≫ c := by rw [← Category.assoc, hρ, hρ₀c]
  exact ⟨((Scheme.Modules.pullbackCongr key).app L).trans ((((Scheme.Modules.pullbackComp ρ ((Scheme.Opens.ι ((TopologicalSpace.Opens.map f₁.base).obj U₁)) ≫ c)).app L).symm).trans (((Scheme.Modules.pullback ρ).mapIso ((((Scheme.Modules.pullbackComp (Scheme.Opens.ι ((TopologicalSpace.Opens.map f₁.base).obj U₁)) c).app L).symm).trans (Φ.trans ((Scheme.Modules.pullbackComp (Scheme.Opens.ι ((TopologicalSpace.Opens.map f₁.base).obj U₁)) c).app M)))).trans (((Scheme.Modules.pullbackComp ρ ((Scheme.Opens.ι ((TopologicalSpace.Opens.map f₁.base).obj U₁)) ≫ c)).app M).trans ((Scheme.Modules.pullbackCongr key.symm).app M))))⟩


-- created on 2026-10-20
