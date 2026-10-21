import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_exists_isOpenImmersion_of_isIso_stalkMap_of_locallyOfFiniteType](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_exists_isOpenImmersion_of_isIso_stalkMap_of_locallyOfFiniteType.lean)
-/
@[path]
private lemma main
  {X Y : (Scheme : Type (u + 1))} (f : X ⟶ Y) [LocallyOfFiniteType f] [IsLocallyNoetherian Y]
  (x : X) [IsIso (f.stalkMap x)] :
    ∃ U : X.Opens, x ∈ U ∧ IsOpenImmersion (U.ι ≫ f) := by
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨V, hV, g, hg1, hg2⟩ := spread_out_of_isGermInjective (sX := 𝟙 Y) (sY := f) (x := f x) (y := x) rfl (inv (f.stalkMap x)) (by simp [TopCat.Presheaf.stalkSpecializes_refl])
  rw [Category.comp_id] at hg2
  let W₀ : X.Opens := ((TopologicalSpace.Opens.map f.base).obj V)
  have hxW₀ : x ∈ W₀ := hV
  have hrange : Set.range (W₀.ι ≫ f) ⊆ Set.range V.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
    apply w.2
  let fV : (W₀ : (Scheme : Type (u + 1))) ⟶ V := IsOpenImmersion.lift V.ι (W₀.ι ≫ f) hrange
  have hfV : fV ≫ V.ι = W₀.ι ≫ f := IsOpenImmersion.lift_fac _ _ _
  let k : (W₀ : (Scheme : Type (u + 1))) ⟶ X := fV ≫ g
  have hk₀ : W₀.fromSpecStalkOfMem x hxW₀ ≫ k = W₀.fromSpecStalkOfMem x hxW₀ ≫ W₀.ι := by
    have h1 : W₀.fromSpecStalkOfMem x hxW₀ ≫ fV = Spec.map (f.stalkMap x) ≫ V.fromSpecStalkOfMem (f x) hV := by
      rw [← cancel_mono V.ι, Category.assoc, hfV, Scheme.Opens.fromSpecStalkOfMem_ι_assoc, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.SpecMap_stalkMap_fromSpecStalk]
    change W₀.fromSpecStalkOfMem x hxW₀ ≫ fV ≫ g = _
    rw [← Category.assoc, h1, Category.assoc, ← hg1, ← Category.assoc, ← Spec.map_comp, IsIso.inv_hom_id, Spec.map_id, Category.id_comp, Scheme.Opens.fromSpecStalkOfMem_ι]
  have hk : (W₀ : (Scheme : Type (u + 1))).fromSpecStalk ⟨x, hxW₀⟩ ≫ k = (W₀ : (Scheme : Type (u + 1))).fromSpecStalk ⟨x, hxW₀⟩ ≫ W₀.ι := by
    have := hk₀
    simp only [Scheme.Opens.fromSpecStalkOfMem, Category.assoc] at this
    apply (cancel_epi _).mp this
  obtain ⟨W, hxW, hW⟩ := spread_out_unique_of_isGermInjective' k W₀.ι hk
  let jW : (W : (Scheme : Type (u + 1))) ⟶ X := W.ι ≫ W₀.ι
  let U : X.Opens := jW.opensRange
  have hxU : x ∈ U := ⟨⟨⟨x, hxW₀⟩, hxW⟩, rfl⟩
  let V' : (V : (Scheme : Type (u + 1))).Opens := ((TopologicalSpace.Opens.map g.base).obj U)
  have hkW : W.ι ≫ k = jW := hW
  have hα_range : Set.range (W.ι ≫ fV) ⊆ Set.range V'.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    change g ((W.ι ≫ fV) w) ∈ U
    rw [← Scheme.Hom.comp_apply, Category.assoc]
    change (W.ι ≫ k) w ∈ U
    rw [hkW]
    refine ⟨w, rfl⟩
  let α : (W : (Scheme : Type (u + 1))) ⟶ V' := IsOpenImmersion.lift V'.ι (W.ι ≫ fV) hα_range
  have hα : α ≫ V'.ι = W.ι ≫ fV := IsOpenImmersion.lift_fac _ _ _
  have hβ_range : Set.range (V'.ι ≫ g) ⊆ Set.range jW := by
    rintro _ ⟨v, rfl⟩
    apply v.2
  let β : (V' : (Scheme : Type (u + 1))) ⟶ W := IsOpenImmersion.lift jW (V'.ι ≫ g) hβ_range
  have hβ : β ≫ jW = V'.ι ≫ g := IsOpenImmersion.lift_fac _ _ _
  have hαβ : α ≫ β = 𝟙 _ := by
    rwa [← cancel_mono jW, Category.assoc, hβ, ← Category.assoc, hα, Category.assoc, Category.id_comp]
  have hβα : β ≫ α = 𝟙 _ := by
    rw [← cancel_mono (V'.ι ≫ V.ι), Category.assoc, ← Category.assoc α, hα, Category.assoc, hfV, Category.id_comp]
    rw [← Category.assoc W.ι, ← Category.assoc β, hβ, Category.assoc, hg2]
  let _ : IsIso α := ⟨⟨β, hαβ, hβα⟩⟩
  have hrangeι : Set.range U.ι = Set.range jW := by
    rw [Scheme.Opens.range_ι]
    rfl
  have hUι : U.ι = (IsOpenImmersion.isoOfRangeEq U.ι jW hrangeι).hom ≫ jW :=
    (IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _).symm
  refine ⟨U, hxU, ?_⟩
  have hjWf : jW ≫ f = α ≫ V'.ι ≫ V.ι := by
    rw [← Category.assoc α, hα]
    simp only [jW, Category.assoc, hfV]
  rw [hUι, Category.assoc, hjWf]
  infer_instance


-- created on 2026-10-20
