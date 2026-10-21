import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_exists_forall_gammaSpecIso_appLE_specMap_comp_eq_div_pow](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_exists_forall_gammaSpecIso_appLE_specMap_comp_eq_div_pow.lean)
-/
@[path]
private lemma main
  {K : Type u} [Field K] {S : Type u} [CommRing S] [Algebra K S]
  {Y : (Scheme : Type (u + 1))} (P : Spec (CommRingCat.of S) ⟶ Y) (V : Y.Opens) (φ : Y.presheaf.obj (op V))
  (σ₁ : AlgHom K S K) (h₁ : ⊤ ≤ ((TopologicalSpace.Opens.map (Spec.map (CommRingCat.ofHom σ₁.toRingHom) ≫ P).base).obj V)) :
    ∃ (s₀ a : S) (k : ℕ), σ₁ s₀ ≠ 0 ∧ ∀ σ : AlgHom K S K, σ s₀ ≠ 0 → ∃ h : ⊤ ≤ ((TopologicalSpace.Opens.map (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ P).base).obj V), (Scheme.ΓSpecIso (CommRingCat.of K)).hom (((Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ P).appLE V ⊤ h) φ) = σ a / σ s₀ ^ k := by
  classical
  have hpt : ∀ (σ : AlgHom K S K) (x : Spec (CommRingCat.of K)) (s : S), (Spec.map (CommRingCat.ofHom σ.toRingHom)).base x ∈ PrimeSpectrum.basicOpen s ↔ σ s ≠ 0 := by
    intro σ x s
    have hx : x.asIdeal = ⊥ := @Ideal.eq_bot_of_prime K _ x.asIdeal x.isPrime
    change x ∈ ((TopologicalSpace.Opens.map (Spec.map (CommRingCat.ofHom σ.toRingHom)).base).obj (PrimeSpectrum.basicOpen s)) ↔ _
    rw [AlgebraicGeometry.SpecMap_preimage_basicOpen]
    change (CommRingCat.ofHom σ.toRingHom).hom s ∉ x.asIdeal ↔ _
    rw [hx, Ideal.mem_bot]
    rfl
  have hx₁ : (Spec.map (CommRingCat.ofHom σ₁.toRingHom)).base default ∈ (((TopologicalSpace.Opens.map P.base).obj V) : Set _) := by
    have := h₁ (TopologicalSpace.Opens.mem_top (default : ↥(Spec (CommRingCat.of K))))
    rwa [Scheme.Hom.comp_preimage] at this
  obtain ⟨_, ⟨s₀, rfl⟩, hs₀mem, hs₀le⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := S)).exists_subset_of_mem_open hx₁ ((TopologicalSpace.Opens.map P.base).obj V).2
  have hσ₁ : σ₁ s₀ ≠ 0 := (hpt σ₁ default s₀).mp hs₀mem
  have hs₀le' : (PrimeSpectrum.basicOpen s₀ : (Spec (CommRingCat.of S)).Opens) ≤ (TopologicalSpace.Opens.map P.base).obj V := hs₀le
  set f : (Spec (CommRingCat.of S)).presheaf.obj (op ⊤) := (Scheme.ΓSpecIso (CommRingCat.of S)).inv s₀ with hfdef
  have hB : (Spec (CommRingCat.of S)).basicOpen f = PrimeSpectrum.basicOpen s₀ :=
    AlgebraicGeometry.basicOpen_eq_of_affine (R := CommRingCat.of S) s₀
  have hBle : (Spec (CommRingCat.of S)).basicOpen f ≤ (TopologicalSpace.Opens.map P.base).obj V := by
    rwa [hB]
  let _ := (isAffineOpen_top (Spec (CommRingCat.of S))).isLocalization_basicOpen f
  set ψ : (Spec (CommRingCat.of S)).presheaf.obj (op ((Spec (CommRingCat.of S)).basicOpen f)) :=
    P.appLE V ((Spec (CommRingCat.of S)).basicOpen f) hBle φ
  obtain ⟨⟨a', ⟨_, k, rfl⟩⟩, hψ⟩ := IsLocalization.surj (Submonoid.powers f) ψ
  refine ⟨s₀, (Scheme.ΓSpecIso (CommRingCat.of S)).hom a', k, hσ₁, fun σ hσ => ?_⟩
  have hσB : ⊤ ≤ (TopologicalSpace.Opens.map (Spec.map (CommRingCat.ofHom σ.toRingHom)).base).obj ((Spec (CommRingCat.of S)).basicOpen f) := by
    intro x _
    show (Spec.map (CommRingCat.ofHom σ.toRingHom)).base x ∈ (Spec (CommRingCat.of S)).basicOpen f
    rw [hB]
    apply (hpt σ x s₀).mpr hσ
  have h : ⊤ ≤ ((TopologicalSpace.Opens.map (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ P).base).obj V) := by
    rw [Scheme.Hom.comp_preimage]
    apply hσB.trans (Scheme.Hom.preimage_mono _ hBle)
  refine ⟨h, ?_⟩
  let χ : RingHom ((Spec (CommRingCat.of S)).presheaf.obj (op ((Spec (CommRingCat.of S)).basicOpen f))) K :=
    ((Spec.map (CommRingCat.ofHom σ.toRingHom)).appLE ((Spec (CommRingCat.of S)).basicOpen f) ⊤ hσB ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom
  have hχ : ∀ x : (Spec (CommRingCat.of S)).presheaf.obj (op ⊤), χ (algebraMap ((Spec (CommRingCat.of S)).presheaf.obj (op ⊤)) ((Spec (CommRingCat.of S)).presheaf.obj (op ((Spec (CommRingCat.of S)).basicOpen f))) x) = σ ((Scheme.ΓSpecIso (CommRingCat.of S)).hom x) := by
    intro x
    show (((Spec (CommRingCat.of S)).presheaf.map (homOfLE ((Spec (CommRingCat.of S)).basicOpen_le f)).op ≫ (Spec.map (CommRingCat.ofHom σ.toRingHom)).appLE ((Spec (CommRingCat.of S)).basicOpen f) ⊤ hσB) ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom x = _
    rw [Scheme.Hom.map_appLE]
    have e1 : (Spec.map (CommRingCat.ofHom σ.toRingHom)).appLE ⊤ ⊤ (by rw [Scheme.Hom.preimage_top]) = (Spec.map (CommRingCat.ofHom σ.toRingHom)).appTop := by
      simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
    rw [e1, Scheme.ΓSpecIso_naturality]
    rfl
  have hval : (Scheme.ΓSpecIso (CommRingCat.of K)).hom (((Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ P).appLE V ⊤ h) φ) = χ ψ := by
    show ((Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ P).appLE V ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom φ = ((P.appLE V ((Spec (CommRingCat.of S)).basicOpen f) hBle ≫ (Spec.map (CommRingCat.ofHom σ.toRingHom)).appLE ((Spec (CommRingCat.of S)).basicOpen f) ⊤ hσB) ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom φ
    rw [Scheme.Hom.appLE_comp_appLE]
  rw [hval]
  have key := congrArg χ hψ
  simp only [map_mul, map_pow] at key
  rw [hχ, hχ] at key
  have hf : (Scheme.ΓSpecIso (CommRingCat.of S)).hom f = s₀ := by
    rw [hfdef]
    apply Iso.inv_hom_id_apply _ _
  rw [hf] at key
  rwa [eq_div_iff (pow_ne_zero _ hσ)]


-- created on 2026-10-20
