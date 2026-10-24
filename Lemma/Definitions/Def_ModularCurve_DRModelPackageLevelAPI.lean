import Mathlib
import Lemma.Definitions.Def_ModularCurve_DRModelPackageLevel
import Lemma.Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Lemma.Definitions.Def_AlgebraicGeometry_RelPicardPullback

set_option autoImplicit false

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
open ModularCurve.IgusaScheme

namespace ModularCurve

attribute [local instance] DRModelPackageLevel.neZero_mul

namespace DRLevel

variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime]

section
variable {κ : Type} [CommRing κ] (toκ : R q →+* κ)

@[reassoc (attr := simp)]
theorem sectionFibre_fst (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R q)))) (toBase N₀ q)) :
    sectionFibre ε toκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom toκ) ≫ ε.1 :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem sectionFibre_snd (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R q)))) (toBase N₀ q)) :
    sectionFibre ε toκ ≫ pullback.snd _ _ = 𝟙 _ :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem fibreMap_fst (φ : X N₀ q ⟶ X N₀ q) (hφ : φ ≫ toBase N₀ q = toBase N₀ q) :
    fibreMap φ hφ toκ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ φ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem fibreMap_snd (φ : X N₀ q ⟶ X N₀ q) (hφ : φ ≫ toBase N₀ q = toBase N₀ q) :
    fibreMap φ hφ toκ ≫ pullback.snd _ _ = pullback.snd _ _ := by
  rw [fibreMap]; exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

@[reassoc (attr := simp)]
theorem fibreMap0_fst (π : SchemeHomOver (toBase N₀ q) (toBase0 N₀ q)) :
    fibreMap0 π toκ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ π.1 :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem fibreMap0_snd (π : SchemeHomOver (toBase N₀ q) (toBase0 N₀ q)) :
    fibreMap0 π toκ ≫ pullback.snd _ _ = pullback.snd _ _ := by
  rw [fibreMap0]; exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

theorem fibreMap_id : fibreMap (𝟙 (X N₀ q)) (Category.id_comp _) toκ = 𝟙 (fibre (N₀ := N₀) toκ) := by
  apply pullback.hom_ext <;> simp

theorem fibreMap_comp (φ ψ : X N₀ q ⟶ X N₀ q) (hφ : φ ≫ toBase N₀ q = toBase N₀ q) (hψ : ψ ≫ toBase N₀ q = toBase N₀ q) :
    fibreMap (φ ≫ ψ) (by rw [Category.assoc, hψ, hφ]) toκ = fibreMap φ hφ toκ ≫ fibreMap ψ hψ toκ := by
  apply pullback.hom_ext <;> simp

theorem fibreMap_comp_fibreMap0 (φ : X N₀ q ⟶ X N₀ q) (hφ : φ ≫ toBase N₀ q = toBase N₀ q)
    (π : SchemeHomOver (toBase N₀ q) (toBase0 N₀ q)) :
    fibreMap φ hφ toκ ≫ fibreMap0 π toκ = fibreMap0 ⟨φ ≫ π.1, by rw [Category.assoc, π.2, hφ]⟩ toκ := by
  apply pullback.hom_ext <;> simp

theorem sectionFibre_comp_fibreMap (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R q)))) (toBase N₀ q))
    (φ : X N₀ q ⟶ X N₀ q) (hφ : φ ≫ toBase N₀ q = toBase N₀ q) :
    sectionFibre ε toκ ≫ fibreMap φ hφ toκ = sectionFibre ⟨ε.1 ≫ φ, by rw [Category.assoc, hφ, ε.2]⟩ toκ := by
  apply pullback.hom_ext <;> simp

end

section
variable {A : Type} [CommRing A] [IsLocalRing A] (ρ : R q →+* A)
  (s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ q))

@[reassoc (attr := simp)]
theorem sectionFibreOver_fst :
    sectionFibreOver ρ s ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ s.1 :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem sectionFibreOver_snd : sectionFibreOver ρ s ≫ pullback.snd _ _ = 𝟙 _ :=
  pullback.lift_snd _ _ _

theorem sectionFibreOver_specMap_comp (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R q)))) (toBase N₀ q)) :
    sectionFibreOver ρ ⟨Spec.map (CommRingCat.ofHom ρ) ≫ ε.1, by rw [Category.assoc, ε.2, Category.comp_id]⟩ =
      sectionFibre ε ((IsLocalRing.residue A).comp ρ) := by
  apply pullback.hom_ext
  · rw [sectionFibreOver_fst, sectionFibre_fst]
    show Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ (Spec.map (CommRingCat.ofHom ρ) ≫ ε.1) =
      Spec.map (CommRingCat.ofHom ((IsLocalRing.residue A).comp ρ)) ≫ ε.1
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  · rw [sectionFibreOver_snd, sectionFibre_snd]

end

section curveChange
variable {κ : Type} [CommRing κ] (toκ : R q →+* κ)

theorem fibreMap0_eq_curveChange (π : SchemeHomOver (toBase N₀ q) (toBase0 N₀ q)) :
    fibreMap0 π toκ = RelPicard.curveChange π.1 π.2 (Spec.map (CommRingCat.ofHom toκ)) := rfl

theorem fibreMap_eq_curveChange (φ : X N₀ q ⟶ X N₀ q) (hφ : φ ≫ toBase N₀ q = toBase N₀ q) :
    fibreMap φ hφ toκ = RelPicard.curveChange φ hφ (Spec.map (CommRingCat.ofHom toκ)) := rfl

end curveChange

section bridges
variable (κ : Type) [CommRing κ] [Algebra (R q) κ]

theorem fibre_eq_pullback_specMap :
    fibre (N₀ := N₀) (algebraMap (R q) κ) = pullback (toBase N₀ q) (SmoothProperCurve.specMap (R q) κ) := rfl

theorem fibre_snd_eq_baseChange :
    pullback.snd (toBase N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (R q) κ))) =
      SmoothProperCurve.baseChange (R q) (toBase N₀ q) κ := rfl

theorem fibre0_eq_pullback_specMap :
    fibre0 (N₀ := N₀) (algebraMap (R q) κ) = pullback (toBase0 N₀ q) (SmoothProperCurve.specMap (R q) κ) := rfl

theorem fibre0_snd_eq_baseChange :
    pullback.snd (toBase0 N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (R q) κ))) =
      SmoothProperCurve.baseChange (R q) (toBase0 N₀ q) κ := rfl

theorem sectionFibre_eq_sectionBaseChange (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R q)))) (toBase N₀ q)) :
    sectionFibre ε (algebraMap (R q) κ) = (SmoothProperCurve.sectionBaseChange κ ε).1 := rfl

end bridges

end DRLevel

open DRLevel

namespace DRModelPackageLevel

variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime] {hqN : ¬ q ∣ N₀} (𝔛 : DRModelPackageLevel N₀ q hqN)

section
variable {κ : Type} [CommRing κ] (toκ : R q →+* κ)

theorem fibreMap_w_w : fibreMap 𝔛.w.hom 𝔛.w_over toκ ≫ fibreMap 𝔛.w.hom 𝔛.w_over toκ = 𝟙 _ := by
  apply pullback.hom_ext <;> simp [𝔛.w_invol]

theorem fibreMap0_πw : fibreMap0 𝔛.πw toκ = fibreMap 𝔛.w.hom 𝔛.w_over toκ ≫ fibreMap0 𝔛.π toκ := by
  apply pullback.hom_ext <;> simp [DRModelPackageLevel.πw]

theorem sectionFibre_εinf_fibreMap_w :
    sectionFibre 𝔛.εinf toκ ≫ fibreMap 𝔛.w.hom 𝔛.w_over toκ = sectionFibre 𝔛.εzero toκ := by
  apply pullback.hom_ext <;> simp [𝔛.w_sections]

@[reassoc (attr := simp)]
theorem εinf0_snd : 𝔛.εinf0 toκ ≫ pullback.snd _ _ = 𝟙 _ := by
  simp [DRModelPackageLevel.εinf0]

end

section
variable {κ : Type} [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : R q →+* κ)

theorem comp1_fibreMap_w : 𝔛.comp κ toκ 1 ≫ fibreMap 𝔛.w.hom 𝔛.w_over toκ = 𝔛.comp κ toκ 0 := by
  rw [← 𝔛.comp_w κ toκ, Category.assoc, fibreMap_w_w, Category.comp_id]

theorem comp1_πw : 𝔛.comp κ toκ 1 ≫ fibreMap0 𝔛.πw toκ = 𝟙 _ := by
  rw [fibreMap0_πw, ← Category.assoc, comp1_fibreMap_w, 𝔛.comp_pi]

theorem comp0_πw : 𝔛.comp κ toκ 0 ≫ fibreMap0 𝔛.πw toκ = 𝔛.comp κ toκ 1 ≫ fibreMap0 𝔛.π toκ := by
  rw [fibreMap0_πw, ← Category.assoc, 𝔛.comp_w]

theorem eq_εinf0_of_comp_comp0 (e : Spec (CommRingCat.of κ) ⟶ fibre0 (N₀ := N₀) toκ)
    (h : e ≫ 𝔛.comp κ toκ 0 = sectionFibre 𝔛.εinf toκ) : e = 𝔛.εinf0 toκ := by
  show e = sectionFibre 𝔛.εinf toκ ≫ fibreMap0 𝔛.π toκ
  rw [← h, Category.assoc, 𝔛.comp_pi, Category.comp_id]

theorem εinf0_comp0_assoc {Z : Scheme.{0}} (g : fibre (N₀ := N₀) toκ ⟶ Z) :
    𝔛.εinf0 toκ ≫ 𝔛.comp κ toκ 0 ≫ g = sectionFibre 𝔛.εinf toκ ≫ g := by
  simpa only [Category.assoc] using congrArg (· ≫ g) (𝔛.εinf0_comp0 κ toκ)

theorem εinf0_comp1_assoc {Z : Scheme.{0}} (g : fibre (N₀ := N₀) toκ ⟶ Z) :
    𝔛.εinf0 toκ ≫ 𝔛.comp κ toκ 1 ≫ g = sectionFibre 𝔛.εzero toκ ≫ g := by
  simpa only [Category.assoc] using congrArg (· ≫ g) (𝔛.εinf0_comp1 κ toκ)

theorem fibre0_snd_eq :
    pullback.snd (toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ)) = inv (𝔛.efib κ toκ) ≫ (𝔛.Mfib κ toκ).toBase := by
  rw [IsIso.eq_inv_comp, 𝔛.hefib]

include 𝔛 in
theorem isProper_fibre0 : IsProper (pullback.snd (toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) := by
  rw [𝔛.fibre0_snd_eq toκ]; infer_instance

include 𝔛 in
theorem smoothOfRelativeDimension_one_fibre0 :
    SmoothOfRelativeDimension 1 (pullback.snd (toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) := by
  rw [𝔛.fibre0_snd_eq toκ]
  exact MorphismProperty.RespectsIso.precomp (P := @SmoothOfRelativeDimension 1) _ _ inferInstance

include 𝔛 in
theorem isIntegral_fibre0 : IsIntegral (fibre0 (N₀ := N₀) toκ) :=
  haveI : Nonempty ↥(fibre0 (N₀ := N₀) toκ) := ⟨(𝔛.efib κ toκ).base (Nonempty.some inferInstance)⟩
  isIntegral_of_isOpenImmersion (inv (𝔛.efib κ toκ))

include 𝔛 in

theorem isProper_fibre : IsProper (pullback.snd (toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))) :=
  MorphismProperty.pullback_snd (P := @IsProper) _ _ 𝔛.isProper

theorem fibre_section_eq_zero_of_comp_app_eq_zero (U : (fibre (N₀ := N₀) toκ).Opens) (s : Γ(fibre (N₀ := N₀) toκ, U))
    (h0 : ((𝔛.comp κ toκ 0).app U).hom s = 0) (h1 : ((𝔛.comp κ toκ 1).app U).hom s = 0) : s = 0 := by
  haveI := 𝔛.fibre_reduced κ toκ
  rw [← basicOpen_eq_bot_iff]
  ext x
  simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
  intro hx
  rcases 𝔛.comp_jointly_surjective κ toκ x with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · have hy : y ∈ (𝔛.comp κ toκ 0) ⁻¹ᵁ ((fibre (N₀ := N₀) toκ).basicOpen s) := hx
    rw [Scheme.preimage_basicOpen] at hy
    have : ((𝔛.comp κ toκ 0).app U).hom s = (𝔛.comp κ toκ 0).app U s := rfl
    rw [← this, h0, Scheme.basicOpen_zero] at hy
    exact hy
  · have hy : y ∈ (𝔛.comp κ toκ 1) ⁻¹ᵁ ((fibre (N₀ := N₀) toκ).basicOpen s) := hx
    rw [Scheme.preimage_basicOpen] at hy
    have : ((𝔛.comp κ toκ 1).app U).hom s = (𝔛.comp κ toκ 1).app U s := rfl
    rw [← this, h1, Scheme.basicOpen_zero] at hy
    exact hy

end

end DRModelPackageLevel

end ModularCurve

end
