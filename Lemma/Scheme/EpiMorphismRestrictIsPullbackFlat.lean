import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

private lemma injective_comp {R S T : CommRingCat.{0}} (f : R ⟶ S) (g : S ⟶ T)
    (hf : Function.Injective f) (hg : Function.Injective g) : Function.Injective (f ≫ g) := by
  intro a b h
  simp only [CommRingCat.comp_apply] at h
  exact hf (hg h)
private lemma injective_of_injective_comp {R S T : CommRingCat.{0}} (f : R ⟶ S) (g : S ⟶ T)
    (h : Function.Injective (f ≫ g)) : Function.Injective f := by
  intro a b hab
  apply h
  simp only [CommRingCat.comp_apply, hab]
private lemma injective_map_eqToHom_op {X : Scheme.{0}} {W₁ W₂ : X.Opens} (h : W₁ = W₂) :
    Function.Injective (X.presheaf.map (eqToHom h).op) := by
  subst h
  intro a b hab
  simpa using hab
private lemma c_eq_of_mk_eq_mk {X Y : PresheafedSpace CommRingCat.{0}} {b : (X : TopCat) ⟶ (Y : TopCat)}
    {c₁ c₂ : Y.presheaf ⟶ b _* X.presheaf}
    (e : (⟨b, c₁⟩ : X ⟶ Y) = ⟨b, c₂⟩) : c₁ = c₂ := by
  cases e
  rfl
private lemma epi_of_base_surjective_of_mono_c_app
    {X Y : PresheafedSpace CommRingCat.{0}} (f : X ⟶ Y)
    (h₁ : Function.Surjective f.base) (h₂ : ∀ U, Mono (f.c.app U)) : Epi f := by
  constructor
  intro Z ⟨g, gc⟩ ⟨h, hc⟩ e
  have eb := congr_arg PresheafedSpace.Hom.base e
  simp only [PresheafedSpace.comp_base] at eb
  let _ : Epi f.base := (TopCat.epi_iff_surjective _).mpr h₁
  obtain rfl : g = h := (cancel_epi f.base).mp eb
  have ec : gc ≫ (TopCat.Presheaf.pushforward _ g).map f.c =
      hc ≫ (TopCat.Presheaf.pushforward _ g).map f.c :=
    c_eq_of_mk_eq_mk (b := f.base ≫ g) e
  let _ : ∀ U, Mono (((TopCat.Presheaf.pushforward CommRingCat.{0} g).map f.c).app U) :=
    fun U ↦ h₂ _
  let _ : Mono ((TopCat.Presheaf.pushforward CommRingCat.{0} g).map f.c) :=
    NatTrans.mono_of_mono_app _
  obtain rfl : gc = hc := (cancel_mono _).mp ec
  rfl
private lemma epi_of_surjective_of_injective_app {X Y : Scheme.{0}} (f : X ⟶ Y) [Surjective f]
    (hinj : ∀ V : Y.Opens, Function.Injective (f.app V)) : Epi f := by
  apply Functor.epi_of_epi_map Scheme.forgetToLocallyRingedSpace
  apply Functor.epi_of_epi_map LocallyRingedSpace.forgetToSheafedSpace
  apply Functor.epi_of_epi_map SheafedSpace.forgetToPresheafedSpace
  apply epi_of_base_surjective_of_mono_c_app _ ‹Surjective f›.surj
  intro U
  exact ConcreteCategory.mono_of_injective _ (hinj U.unop)
private lemma epi_morphismRestrict_of_surjective_of_injective_app
    {X Y : Scheme.{0}} (f : X ⟶ Y) [Surjective f]
    (hinj : ∀ V : Y.Opens, Function.Injective (f.app V)) (U : Y.Opens) : Epi (f ∣_ U) := by
  let _ : Surjective (f ∣_ U) := IsZariskiLocalAtTarget.restrict ‹Surjective f› U
  refine epi_of_surjective_of_injective_app (f ∣_ U) fun V ↦ ?_
  rw [morphismRestrict_app]
  exact injective_comp _ _ (hinj _) (injective_map_eqToHom_op (image_morphismRestrict_preimage f U V))
private lemma injective_app_of_forall_epi_morphismRestrict
    {X Y : Scheme.{0}} (p : X ⟶ Y) (hp : ∀ U : Y.Opens, Epi (p ∣_ U)) (V : Y.Opens) :
    Function.Injective (p.app V) := by
  have h1 : Mono (p ∣_ V).appTop := by
    let _ := Functor.preservesEpimorphisms_of_adjunction ΓSpec.adjunction
    let _ := hp V
    have h : Epi (Scheme.Γ.rightOp.map (p ∣_ V)) := inferInstance
    have h' : Mono (Scheme.Γ.map (p ∣_ V).op) := (op_epi_iff _).mp h
    rwa [Scheme.Γ_map_op] at h'
  have h2 : Function.Injective (p ∣_ V).appTop :=
    ConcreteCategory.injective_of_mono_of_preservesPullback _
  rw [morphismRestrict_appTop] at h2
  have h3 : Function.Injective (p.app (V.ι ''ᵁ ⊤)) := injective_of_injective_comp _ _ h2
  rwa [Scheme.Opens.ι_image_top] at h3
private lemma injective_app_of_isPullback_of_flat
    {X Y X' Y' : Scheme.{0}} (p : X ⟶ Y) [IsAffineHom p] (f : Y' ⟶ Y) [Flat f]
    (p' : X' ⟶ Y') (q : X' ⟶ X) (sq : IsPullback q p' p f)
    (hp : ∀ V : Y.Opens, Function.Injective (p.app V)) (V' : Y'.Opens) :
    Function.Injective (p'.app V') := by
  have key : ∀ {W : Y.Opens} (_ : IsAffineOpen W) {W' : Y'.Opens} (_ : IsAffineOpen W')
      (_ : W' ≤ f ⁻¹ᵁ W), Function.Injective (p'.app W') := by
    intro W hW W' hW' hle
    have hpW : IsAffineOpen (p ⁻¹ᵁ W) := hW.preimage p
    let hiso := isIso_pushoutSection_of_isAffineOpen sq hle (le_refl (p ⁻¹ᵁ W)) rfl hW hW' hpW
    have h1 : pushout.inr _ _ ≫ pushoutSection sq hle (le_refl (p ⁻¹ᵁ W)) rfl =
        p'.appLE W' (q ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ W') inf_le_right :=
      pushout.inr_desc _ _ _
    have h2 : Function.Injective (p'.appLE W' (q ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ W') inf_le_right) := by
      rw [← h1]
      refine injective_comp _ _ ?_ (ConcreteCategory.injective_of_mono_of_preservesPullback _)
      refine CommRingCat.inr_injective_of_flat _ _ ?_ (f.flat_appLE hW hW' hle)
      rw [Scheme.Hom.appLE_eq_app]
      exact hp W
    rw [Scheme.Hom.appLE] at h2
    exact injective_of_injective_comp _ _ h2
  intro s t hst
  apply Y'.IsSheaf.section_ext
  intro y hy
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f y)) isOpen_univ
  obtain ⟨_, ⟨W', hW', rfl⟩, hyW', hW'le⟩ :=
    Y'.isBasis_affineOpens.exists_subset_of_mem_open (a := y) (show y ∈ (f ⁻¹ᵁ W ⊓ V' : Y'.Opens)
      from ⟨hyW, hy⟩) (f ⁻¹ᵁ W ⊓ V').isOpen
  have hW'le' : W' ≤ f ⁻¹ᵁ W ⊓ V' := hW'le
  refine ⟨W', hW'le'.trans inf_le_right, hyW', ?_⟩
  apply key hW hW' (hW'le'.trans inf_le_left)
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, p'.naturality, CommRingCat.comp_apply,
    CommRingCat.comp_apply, hst]
/--
[AlgebraicGeometry_epi_morphismRestrict_of_isPullback_of_flat](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_epi_morphismRestrict_of_isPullback_of_flat.lean)
-/
@[path]
private lemma main
    {X Y X' Y' : Scheme.{0}} (p : X ⟶ Y) [IsAffineHom p] [Surjective p]
    (f : Y' ⟶ Y) [Flat f] (p' : X' ⟶ Y') (q : X' ⟶ X) (sq : IsPullback q p' p f)
    (hp : ∀ U : Y.Opens, Epi (p ∣_ U)) (U' : Y'.Opens) : Epi (p' ∣_ U') := by
  let _ : Surjective p' := MorphismProperty.of_isPullback (P := @Surjective) sq ‹Surjective p›
  exact epi_morphismRestrict_of_surjective_of_injective_app p'
    (injective_app_of_isPullback_of_flat p f p' q sq (injective_app_of_forall_epi_morphismRestrict p hp)) U'

-- created on 2026-10-20
