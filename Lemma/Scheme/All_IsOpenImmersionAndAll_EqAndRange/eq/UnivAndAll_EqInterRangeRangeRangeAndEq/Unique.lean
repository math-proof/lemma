import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma some_hom_eq
  {J : Type u} {k i : J} (a : WidePushoutShape.Hom (some k) (some i)) :
    k = i := by
  match a with
  | .id _ => rfl

/--
[AlgebraicGeometry_Scheme_exists_glue_forall_isOpenImmersion_of_forall_isOpenImmersion](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_exists_glue_forall_isOpenImmersion_of_forall_isOpenImmersion.lean)
-/
@[path]
private lemma main
  (W : (Scheme : Type (u + 1))) {ι : Type u} [Nonempty ι] (U : ι → (Scheme : Type (u + 1))) (f : ∀ i, W ⟶ U i)
  [∀ i, IsOpenImmersion (f i)] :
    ∃ (Y : (Scheme : Type (u + 1))) (g : ∀ i, U i ⟶ Y), (∀ i, IsOpenImmersion (g i)) ∧
      (∀ i j, f i ≫ g i = f j ≫ g j) ∧
      (⋃ i, Set.range (g i).base = Set.univ) ∧
      (∀ i j, i ≠ j → Set.range (g i).base ∩ Set.range (g j).base = Set.range (f i ≫ g i).base) ∧
      (∀ (Z : (Scheme : Type (u + 1))) (h : ∀ i, U i ⟶ Z), (∀ i j, f i ≫ h i = f j ≫ h j) → ∃! k : Y ⟶ Z, ∀ i, g i ≫ k = h i) := by
  classical
  let F : WidePushoutShape ι ⥤ (Scheme : Type (u + 1)) := WidePushoutShape.wideSpan W U f
  let hF : ∀ {i j : WidePushoutShape ι} (a : i ⟶ j), IsOpenImmersion (F.map a) := by
    rintro i j ⟨⟩
    · exact inferInstanceAs (IsOpenImmersion (𝟙 _))
    · exact inferInstanceAs (IsOpenImmersion (f _))
  let Y : (Scheme : Type (u + 1)) := colimit F
  let g : ∀ i, U i ⟶ Y := fun i => colimit.ι F (some i)
  have hgW : ∀ i, f i ≫ g i = colimit.ι F none := fun i => colimit.w F (WidePushoutShape.Hom.init i)
  refine ⟨Y, g, fun i => inferInstanceAs (IsOpenImmersion (colimit.ι F (some i))), ?_, ?_, ?_, ?_⟩
  ·
    intro i j
    rw [hgW, hgW]
  ·
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨(_ | i), x, hx⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective F y
    ·
      obtain ⟨i⟩ := ‹Nonempty ι›
      refine Set.mem_iUnion.mpr ⟨i, (f i).base x, ?_⟩
      rwa [← Scheme.Hom.comp_apply, hgW]
    · exact Set.mem_iUnion.mpr ⟨i, x, hx⟩
  ·
    intro i j hij
    ext y
    constructor
    ·
      rintro ⟨⟨xi, rfl⟩, ⟨xj, hxj⟩⟩
      obtain ⟨k, fi, fj, x, hfi, hfj⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff F).mp hxj.symm
      cases k
      ·
        obtain rfl : fi = WidePushoutShape.Hom.init i := Subsingleton.elim _ _
        refine ⟨x, ?_⟩
        rw [Scheme.Hom.comp_apply]
        apply congrArg (g i).base hfi
      ·
        apply absurd ((some_hom_eq fi).symm.trans (some_hom_eq fj)) hij
    ·
      rintro ⟨w, rfl⟩
      refine ⟨⟨(f i).base w, by rw [← Scheme.Hom.comp_apply]⟩, ⟨(f j).base w, ?_⟩⟩
      rw [← Scheme.Hom.comp_apply, hgW, hgW]
  ·
    intro Z h hh
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    let c : Cocone F := WidePushoutShape.mkCocone (f i₀ ≫ h i₀) h (fun i => hh i i₀)
    refine ⟨colimit.desc F c, fun i => colimit.ι_desc c (some i), ?_⟩
    intro k hk
    apply colimit.hom_ext
    intro j
    erw [colimit.ι_desc]
    match j with
    | none =>
      show colimit.ι F none ≫ k = f i₀ ≫ h i₀
      rw [← hgW i₀]
      apply (Category.assoc _ _ _).trans (congrArg (fun t => f i₀ ≫ t) (hk i₀))
    | some i =>
      apply hk i


-- created on 2026-10-20
