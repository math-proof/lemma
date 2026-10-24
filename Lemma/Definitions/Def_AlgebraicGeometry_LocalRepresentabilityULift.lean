import Mathlib

set_option autoImplicit false

universe w v u

open CategoryTheory Category Limits Opposite

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C] (P : MorphismProperty C)

abbrev presheafULift : MorphismProperty (Cᵒᵖ ⥤ Type (max w v)) := P.relative uliftYoneda.{w}

variable {P}

lemma presheafULift_monomorphisms_le_monomorphisms :
    presheafULift.{w} (monomorphisms C) ≤ monomorphisms _ := fun F G f hf ↦ by
  suffices ∀ {X : C} {a b : uliftYoneda.{w}.obj X ⟶ F}, a ≫ f = b ≫ f → a = b from
    ⟨fun _ _ h ↦ hom_ext_uliftYoneda (fun _ _ ↦ this (by simp only [assoc, h]))⟩
  intro X a b h
  suffices hf.rep.lift (g := a ≫ f) a (𝟙 X) (by simp) =
      hf.rep.lift b (𝟙 X) (by simp [← h]) by
    simpa using uliftYoneda.{w}.congr_map this =≫ (hf.rep.fst (a ≫ f))
  have : Mono (hf.rep.snd (a ≫ f)) := hf.property_snd (a ≫ f)
  simp only [← cancel_mono (hf.rep.snd (a ≫ f)), Functor.relativelyRepresentable.lift_snd]

variable {G : Cᵒᵖ ⥤ Type (max w v)}

lemma presheafULift_mono_of_le (hP : P ≤ MorphismProperty.monomorphisms C)
    {X : C} {f : uliftYoneda.{w}.obj X ⟶ G} (hf : P.presheafULift f) : Mono f :=
  MorphismProperty.presheafULift_monomorphisms_le_monomorphisms _
    (MorphismProperty.relative_monotone hP _ hf)

lemma fst'_self_eq_snd_ULift (hP : P ≤ MorphismProperty.monomorphisms C)
    {X : C} {f : uliftYoneda.{w}.obj X ⟶ G} (hf : P.presheafULift f) : hf.rep.fst' f = hf.rep.snd f := by
  have := presheafULift_mono_of_le hP hf
  apply uliftYoneda.{w}.map_injective
  rw [← cancel_mono f, (hf.rep.isPullback' f).w]

lemma isIso_fst'_self_ULift (hP : P ≤ MorphismProperty.monomorphisms C)
    {X : C} {f : uliftYoneda.{w}.obj X ⟶ G} (hf : P.presheafULift f) : IsIso (hf.rep.fst' f) :=
  have := presheafULift_mono_of_le hP hf
  have := (hf.rep.isPullback' f).isIso_fst_of_mono
  (ULiftYoneda.fullyFaithful C).isIso_of_isIso_map _

end CategoryTheory.MorphismProperty

namespace AlgebraicGeometry

namespace Scheme

variable (F : Sheaf Scheme.zariskiTopology.{u} (Type (max w u)))
  {ι : Type u} {X : ι → Scheme.{u}}
  (f : (i : ι) → uliftYoneda.{w}.obj (X i) ⟶ F.obj) (hf : ∀ i, MorphismProperty.presheafULift.{w} @IsOpenImmersion (f i))

namespace LocalRepresentabilityULift

variable {F f} (i j k : ι)

set_option backward.isDefEq.respectTransparency false in
open Functor.relativelyRepresentable in

@[simps]
noncomputable def glueData : GlueData where
  J := ι
  U := X
  V := fun (i, j) ↦ (hf i).rep.pullback (f j)
  f i j := (hf i).rep.fst' (f j)
  f_mono i j :=
    have := (hf j).property _ _ _ ((hf i).1.isPullback' (f j)).flip
    IsOpenImmersion.mono _
  f_id i := MorphismProperty.isIso_fst'_self_ULift IsOpenImmersion.le_monomorphisms (hf i)
  t i j := (hf i).rep.symmetry (hf j).rep
  t_id i := by apply (hf i).rep.hom_ext' <;>
    simp [MorphismProperty.fst'_self_eq_snd_ULift IsOpenImmersion.le_monomorphisms (hf i)]
  t' i j k := lift₃ _ _ _ (pullback₃.p₂ _ _ _) (pullback₃.p₃ _ _ _) (pullback₃.p₁ _ _ _)
    (by simp) (by simp)
  t_fac i j k := (hf j).rep.hom_ext' (by simp) (by simp)
  cocycle i j k := pullback₃.hom_ext (by simp) (by simp) (by simp)
  f_open i j := (hf j).property _ _ _ ((hf i).1.isPullback' (f j)).flip

noncomputable def toGlued (i : ι) : X i ⟶ (glueData hf).glued :=
  (glueData hf).ι i

instance : IsOpenImmersion (toGlued hf i) :=
  inferInstanceAs (IsOpenImmersion ((glueData hf).ι i))

set_option backward.isDefEq.respectTransparency false in

noncomputable def uliftYonedaGluedToSheaf :
    (GrothendieckTopology.uliftYoneda.{w} zariskiTopology).obj (glueData hf).glued ⟶ F where
  hom := uliftYonedaEquiv.symm
    ((glueData hf).sheafValGluedMk (fun i ↦ uliftYonedaEquiv (f i)) (by
      intro (i : ι) (j : ι)
      dsimp only [glueData_V, glueData_J, glueData_U, glueData_f, glueData_t]
      rw [uliftYonedaEquiv_naturality, uliftYonedaEquiv_naturality]
      congr 1
      rw [← op_comp, Quiver.Hom.unop_op, Quiver.Hom.unop_op]
      erw [Functor.relativelyRepresentable.symmetry_fst, ((hf i).rep.isPullback' (f j)).w]))

@[reassoc (attr := simp)]
lemma uliftYoneda_toGlued_uliftYonedaGluedToSheaf (i : ι) :
    uliftYoneda.{w}.map (toGlued hf i) ≫ (uliftYonedaGluedToSheaf hf).hom = f i := by
  apply uliftYonedaEquiv.injective
  have h := uliftYonedaEquiv_naturality (uliftYonedaGluedToSheaf hf).hom (toGlued hf i).op
  rw [Quiver.Hom.unop_op] at h
  rw [← h]
  simp only [uliftYonedaGluedToSheaf, toGlued, Equiv.apply_symm_apply]
  exact GlueData.sheafValGluedMk_val _ _ _ _

@[simp]
lemma uliftYonedaGluedToSheaf_app_toGlued {i : ι} :
    dsimp% (uliftYonedaGluedToSheaf hf).hom.app (op (X i)) ⟨toGlued hf i⟩ = uliftYonedaEquiv (f i) := by
  rw [← uliftYoneda_toGlued_uliftYonedaGluedToSheaf hf i, uliftYonedaEquiv_comp,
    uliftYonedaEquiv_uliftYoneda_map]
  rfl

@[simp]
lemma uliftYonedaGluedToSheaf_app_comp {V U : Scheme.{u}} (γ : V ⟶ U) (α : U ⟶ (glueData hf).glued) :
    dsimp% (uliftYonedaGluedToSheaf hf).hom.app (op V) ⟨γ ≫ α⟩ =
      F.obj.map γ.op ((uliftYonedaGluedToSheaf hf).hom.app (op U) ⟨α⟩) :=
  ConcreteCategory.congr_hom ((uliftYonedaGluedToSheaf hf).hom.naturality γ.op) ⟨α⟩

set_option backward.isDefEq.respectTransparency false in
instance [Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f)] :
    Sheaf.IsLocallySurjective (uliftYonedaGluedToSheaf hf) :=
  Presheaf.isLocallySurjective_of_isLocallySurjective_fac _
    (show Sigma.desc (fun i ↦ uliftYoneda.{w}.map (toGlued hf i)) ≫
      (uliftYonedaGluedToSheaf hf).hom = Sigma.desc f by cat_disch)

lemma comp_toGlued_eq {U : Scheme.{u}} {i j : ι} (a : U ⟶ X i) (b : U ⟶ X j)
    (h : uliftYoneda.{w}.map a ≫ f i = uliftYoneda.{w}.map b ≫ f j) :
    a ≫ toGlued hf i = b ≫ toGlued hf j := by
  rw [← (hf i).rep.lift'_fst a b h, assoc]
  conv_rhs => rw [← (hf i).rep.lift'_snd a b h, assoc]
  congr 1
  exact ((glueData hf).glue_condition i j).symm.trans
    (by simp [toGlued]; erw [Functor.relativelyRepresentable.symmetry_fst_assoc])

@[simp]
lemma glueData_openCover_map : (glueData hf).openCover.f j = toGlued hf j := rfl

instance : Sheaf.IsLocallyInjective (uliftYonedaGluedToSheaf hf) where
  equalizerSieve_mem := by
    rintro ⟨U⟩ ⟨α⟩ ⟨β⟩ h
    replace h : (uliftYonedaGluedToSheaf hf).hom.app _ ⟨α⟩ = (uliftYonedaGluedToSheaf hf).hom.app _ ⟨β⟩ := h
    have mem := (glueData hf).openCover.mem_grothendieckTopology
    refine GrothendieckTopology.superset_covering _ ?_
      (zariskiTopology.intersection_covering (zariskiTopology.pullback_stable α mem)
        (zariskiTopology.pullback_stable β mem))
    rintro V (γ : _ ⟶ U) ⟨⟨W₁, a, _, ⟨i⟩, fac₁⟩, ⟨W₂, b, _, ⟨j⟩, fac₂⟩⟩

    change V ⟶ X i at a
    change V ⟶ X j at b
    change a ≫ toGlued hf i = γ ≫ α at fac₁
    change b ≫ toGlued hf j = γ ≫ β at fac₂
    change ULift.up (γ ≫ α) = ULift.up (γ ≫ β)
    replace h : (uliftYonedaGluedToSheaf hf).hom.app _ ⟨γ ≫ α⟩ =
        (uliftYonedaGluedToSheaf hf).hom.app _ ⟨γ ≫ β⟩ := by
      dsimp at h; simp [h]
    rw [← fac₁, ← fac₂] at h ⊢
    apply congrArg ULift.up
    apply comp_toGlued_eq
    simp at h
    apply uliftYonedaEquiv.{w}.injective
    have ha := uliftYonedaEquiv_naturality (X := op (X i)) (f i) a.op
    have hb := uliftYonedaEquiv_naturality (X := op (X j)) (f j) b.op
    exact ha.symm.trans (h.trans hb)

variable [Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f)]

instance : IsIso (uliftYonedaGluedToSheaf hf) := by
  rw [← Sheaf.isLocallyBijective_iff_isIso (uliftYonedaGluedToSheaf hf)]
  constructor <;> infer_instance

noncomputable def uliftYonedaIsoSheaf :
    (GrothendieckTopology.uliftYoneda.{w} zariskiTopology).obj (glueData hf).glued ≅ F :=
  asIso (uliftYonedaGluedToSheaf hf)

noncomputable def representableBy : F.obj.RepresentableBy (glueData hf).glued :=
  (Functor.RepresentableBy.equivUliftYonedaIso.{w} _ _).symm
    ((sheafToPresheaf _ _).mapIso (uliftYonedaIsoSheaf hf))

include hf in
theorem isRepresentable : F.obj.IsRepresentable :=
  ⟨_, ⟨representableBy hf⟩⟩

end LocalRepresentabilityULift

end Scheme

end AlgebraicGeometry
