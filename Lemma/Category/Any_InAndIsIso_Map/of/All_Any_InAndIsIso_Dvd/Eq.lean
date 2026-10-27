import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


private lemma exists_mem_and_preimage_le_of_isClosedMap {X Y : Scheme.{0}} (q : X ⟶ Y)
  (hq : IsClosedMap q.base) (y : Y) (W : X.Opens) (hW : ∀ x : X, q.base x = y → x ∈ W) :
  ∃ V : Y.Opens, y ∈ V ∧ q ⁻¹ᵁ V ≤ W := by
  refine ⟨⟨(q.base '' (W : Set X)ᶜ)ᶜ, (hq _ W.isOpen.isClosed_compl).isOpen_compl⟩, ?_, ?_⟩
  ·
    rintro ⟨x, hx, hxy⟩
    exact hx (hW x hxy)
  ·
    intro x hx
    by_contra hxW
    exact hx ⟨x, hxW, rfl⟩

private lemma isPullback_fst_map_fst {X Y Z W : Scheme.{0}} (p : Z ⟶ Y) (q : X ⟶ Y) (h : Z ⟶ X)
  (w : h ≫ q = p) (g : W ⟶ Y) :
  IsPullback (pullback.fst p g)
    (pullback.map p g q g h (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp]))
    h (pullback.fst q g) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd q g) (v₂₂ := q) (h₃₁ := g) ?_ ?_
    (IsPullback.of_hasPullback q g)
  ·
    have e1 : pullback.map p g q g h (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp]) ≫ pullback.snd q g =
        pullback.snd p g := by rw [pullback.lift_snd, Category.comp_id]
    rw [e1, w]
    exact IsPullback.of_hasPullback p g
  · rw [pullback.lift_fst]
/--
[AlgebraicGeometry_exists_mem_and_isIso_pullbackMap_opens_of_forall_exists_isIso_morphismRestrict](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_exists_mem_and_isIso_pullbackMap_opens_of_forall_exists_isIso_morphismRestrict.lean)
-/
@[path]
private lemma main
  {X Y Z : Scheme.{0}}
  {p : Z ⟶ Y} [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
  {q : X ⟶ Y} [IsProper q] [Flat q] [LocallyOfFinitePresentation q]
  {y : Y}
-- given
  (h : Z ⟶ X)
  (w : h ≫ q = p)
  (hD : ∀ x : X, q.base x = y → ∃ D : X.Opens, x ∈ D ∧ IsIso (h ∣_ D)) :
-- imply
  ∃ V : Y.Opens, y ∈ V ∧
      IsIso (pullback.map p V.ι q V.ι h (𝟙 _) (𝟙 _)
        (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp])) := by
-- proof
  classical
    choose D hxD hDi using fun x : {x : X // q.base x = y} => hD x.1 x.2
    let W : X.Opens := ⨆ x : {x : X // q.base x = y}, D x
    have hW : ∀ x : X, q.base x = y → x ∈ W := fun x hx =>
      TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxD ⟨x, hx⟩⟩
    obtain ⟨V, hyV, hVW⟩ := exists_mem_and_preimage_le_of_isClosedMap q q.isClosedMap y W hW
    refine ⟨V, hyV, ?_⟩
    set hV := pullback.map p V.ι q V.ι h (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp]) with hhV
    let E : {x : X // q.base x = y} → (pullback q V.ι).Opens := fun x => pullback.fst q V.ι ⁻¹ᵁ D x
    have hcover : ⨆ x, E x = ⊤ := by
      refine top_unique fun z _ => ?_
      rw [TopologicalSpace.Opens.mem_iSup]
      have hz : pullback.fst q V.ι z ∈ W := by
        apply hVW
        show q.base (pullback.fst q V.ι z) ∈ V
        rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
        exact (pullback.snd q V.ι z).2
      obtain ⟨x, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
      exact ⟨x, hx⟩
    rw [← MorphismProperty.isomorphisms.iff]
    refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) E hcover fun x => ?_
    have sq2 : IsPullback (pullback.fst p V.ι) hV h (pullback.fst q V.ι) := by
      rw [hhV]; exact isPullback_fst_map_fst p q h w V.ι
    have big : IsPullback (hV ∣_ E x) ((hV ⁻¹ᵁ E x).ι ≫ pullback.fst p V.ι) ((E x).ι ≫ pullback.fst q V.ι) h :=
      (isPullback_morphismRestrict hV (E x)).paste_vert sq2.flip
    have hsubE : Set.range ((E x).ι ≫ pullback.fst q V.ι).base ⊆ Set.range (D x).ι.base := by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact z.2
    let u : ((E x : (pullback q V.ι).Opens) : Scheme.{0}) ⟶ (D x : X.Opens) :=
      IsOpenImmersion.lift (D x).ι ((E x).ι ≫ pullback.fst q V.ι) hsubE
    have hu : u ≫ (D x).ι = (E x).ι ≫ pullback.fst q V.ι := IsOpenImmersion.lift_fac _ _ _
    have hsubF : Set.range ((hV ⁻¹ᵁ E x).ι ≫ pullback.fst p V.ι).base ⊆ Set.range (h ⁻¹ᵁ D x).ι.base := by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      show h.base (((hV ⁻¹ᵁ E x).ι ≫ pullback.fst p V.ι).base z) ∈ D x
      have key : ((hV ⁻¹ᵁ E x).ι ≫ pullback.fst p V.ι) ≫ h = (hV ∣_ E x) ≫ (E x).ι ≫ pullback.fst q V.ι :=
        big.w.symm
      rw [← Scheme.Hom.comp_apply, key, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
      exact ((hV ∣_ E x).base z).2
    let f' : ((hV ⁻¹ᵁ E x : (pullback p V.ι).Opens) : Scheme.{0}) ⟶ (h ⁻¹ᵁ D x : Z.Opens) :=
      IsOpenImmersion.lift (h ⁻¹ᵁ D x).ι ((hV ⁻¹ᵁ E x).ι ≫ pullback.fst p V.ι) hsubF
    have hf' : f' ≫ (h ⁻¹ᵁ D x).ι = (hV ⁻¹ᵁ E x).ι ≫ pullback.fst p V.ι := IsOpenImmersion.lift_fac _ _ _
    have sq : IsPullback f' (hV ∣_ E x) (h ∣_ D x) u := by
      refine IsPullback.of_right (h₁₂ := (h ⁻¹ᵁ D x).ι) (v₁₃ := h) (h₂₂ := (D x).ι) ?_ ?_
        (isPullback_morphismRestrict h (D x)).flip
      ·
        rw [hf', hu]; apply big.flip
      ·
        have hVfst : hV ≫ pullback.fst q V.ι = pullback.fst p V.ι ≫ h := by rw [hhV, pullback.lift_fst]
        rw [← cancel_mono (D x).ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hf', Category.assoc,
          Category.assoc, hu, ← Category.assoc (hV ∣_ E x), morphismRestrict_ι, Category.assoc, hVfst]
    have := hDi x
    exact MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms Scheme) sq
      ((MorphismProperty.isomorphisms.iff _).mpr inferInstance)


-- created on 2026-10-23
