import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_SmoothOfRelativeDimension_nonempty_basis_kaehlerDifferential_stalk_of_fromSpecStalk_comp_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_SmoothOfRelativeDimension_nonempty_basis_kaehlerDifferential_stalk_of_fromSpecStalk_comp_eq.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R]
  {Y : (Scheme : Type (u + 1))}
  (f : Y ⟶ Spec (CommRingCat.of R))
  (n : ℕ) [SmoothOfRelativeDimension n f]
  (y : Y) [Algebra R (Y.presheaf.stalk y)]
  (halg : Y.fromSpecStalk y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y)))) :
  Nonempty (Module.Basis (Fin n) (Y.presheaf.stalk y) Ω[Y.presheaf.stalk y⁄R]) := by
  classical
  obtain ⟨U, hU, V, hV, hyV, e, hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) y
  obtain ⟨r, s, hys, e₁, hf₁⟩ := exists_basicOpen_le_appLE_of_appLE_of_isAffine
    (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).right
    (RingHom.isStandardSmoothOfRelativeDimension_localizationPreserves n).away
    y ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ ⟨V, hV⟩ ⟨V, hV⟩ hyV hyV e hf (by trivial)
  set W : Y.Opens := Y.basicOpen s
  have hWaff : IsAffineOpen W := hV.basicOpen s
  have hyW : y ∈ W := hys
  have eW : W ≤ ((TopologicalSpace.Opens.map f.base).obj (⊤ : (Spec (CommRingCat.of R)).Opens)) :=
    fun x _ => by simp
  let _ : Algebra R (Y.presheaf.obj (op W)) :=
    ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ W eW).hom.toAlgebra
  let _ : Algebra (Y.presheaf.obj (op W)) (Y.presheaf.stalk y) :=
    Y.presheaf.algebra_section_stalk ⟨y, hyW⟩
  have hpin : CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y)) =
      (Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop ≫ Y.presheaf.germ ⊤ y trivial := by
    have h := congrArg Scheme.Hom.appTop halg
    rw [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop] at h
    have h' := congrArg (fun k => (Scheme.ΓSpecIso (.of R)).inv ≫ k ≫ (Scheme.ΓSpecIso (Y.presheaf.stalk y)).hom) h
    simp only [Category.assoc] at h'
    rw [← Scheme.ΓSpecIso_inv_naturality_assoc] at h'
    simpa using h'.symm
  let _ : IsScalarTower R (Y.presheaf.obj (op W)) (Y.presheaf.stalk y) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      show (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y))).hom a =
        (Y.presheaf.germ W y hyW).hom (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ W eW).hom a)
      rw [hpin, ← CommRingCat.comp_apply, Category.assoc, Scheme.Hom.appLE, Category.assoc,
        TopCat.Presheaf.germ_res]
      rfl
  have hstd : Algebra.IsStandardSmoothOfRelativeDimension n R (Y.presheaf.obj (op W)) := by
    have h₁ := (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).left
      _ r _ hf₁
    rw [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE] at h₁
    have h₂ : (f.appLE ⊤ W eW).hom.IsStandardSmoothOfRelativeDimension n := h₁
    have h₃ := ((RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n)).cancel_left_isIso
      (Scheme.ΓSpecIso (.of R)).inv (f.appLE ⊤ W eW)).mpr h₂
    rw [← CommRingCat.hom_comp] at h₃
    apply h₃
  let _ := hstd
  let _ : Algebra.IsStandardSmooth R (Y.presheaf.obj (op W)) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  let _ : Nontrivial (Y.presheaf.obj (op W)) :=
    (algebraMap (Y.presheaf.obj (op W)) (Y.presheaf.stalk y)).domain_nontrivial
  have hrank : Module.rank (Y.presheaf.obj (op W)) Ω[(Y.presheaf.obj (op W))⁄R] = n :=
    Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n
  let _ : Module.Finite (Y.presheaf.obj (op W)) Ω[(Y.presheaf.obj (op W))⁄R] :=
    Module.finite_of_rank_eq_nat hrank
  let bA : Module.Basis (Fin n) (Y.presheaf.obj (op W)) Ω[(Y.presheaf.obj (op W))⁄R] :=
    Module.finBasisOfFinrankEq _ _ (Module.finrank_eq_of_rank_eq hrank)
  let _ := hWaff.isLocalization_stalk ⟨y, hyW⟩
  exact ⟨bA.ofIsLocalizedModule (Y.presheaf.stalk y) (hWaff.primeIdealOf ⟨y, hyW⟩).asIdeal.primeCompl
    (KaehlerDifferential.map R R (Y.presheaf.obj (op W)) (Y.presheaf.stalk y))⟩


-- created on 2026-10-20
