import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_isIso_residueFieldMap_of_comp_eq_fromSpecResidueField](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isIso_residueFieldMap_of_comp_eq_fromSpecResidueField.lean)
-/
@[path]
private lemma main
  {X Y : (Scheme : Type 1)}
  (f : X ⟶ Y)
  (y : Y)
  (u₀ : Spec (Y.residueField y) ⟶ X)
  (hu₀ : u₀ ≫ f = Y.fromSpecResidueField y) :
  IsIso (f.residueFieldMap (u₀.base (IsLocalRing.closedPoint (Y.residueField y)))) := by
  classical
  let _ : IsLocalRing (IsLocalRing.ResidueField ↑(Y.presheaf.stalk y)) :=
    inferInstanceAs (IsLocalRing ↑(Y.residueField y))
  have i1 : IsLocalHom (CommRingCat.Hom.hom (Scheme.stalkClosedPointTo u₀)) :=
    Scheme.isLocalHom_stalkClosedPointTo u₀
  obtain ⟨b, hb⟩ : ∃ b : X.residueField (u₀.base (IsLocalRing.closedPoint (Y.residueField y))) ⟶ Y.residueField y, X.residue _ ≫ b = Scheme.stalkClosedPointTo u₀ :=
    ⟨@Scheme.descResidueField _ _ X _ (Scheme.stalkClosedPointTo u₀) i1, @Scheme.residue_descResidueField _ _ X _ _ i1⟩
  have h1 : Scheme.SpecToEquivOfField (Y.residueField y) Y (u₀ ≫ f) = ⟨y, 𝟙 _⟩ := by
    rw [hu₀, ← (Scheme.SpecToEquivOfField (Y.residueField y) Y).apply_symm_apply ⟨y, 𝟙 _⟩]
    congr 1
    simp [Scheme.SpecToEquivOfField]
    apply (Category.id_comp _).symm
  rw [Scheme.SpecToEquivOfField_eq_iff] at h1
  obtain ⟨e, he⟩ := h1
  simp only [Scheme.SpecToEquivOfField, Equiv.coe_fn_mk, Category.comp_id] at he e
  have i2 : IsLocalHom (CommRingCat.Hom.hom (Scheme.stalkClosedPointTo (u₀ ≫ f))) :=
    Scheme.isLocalHom_stalkClosedPointTo (u₀ ≫ f)
  have h3 : Y.residue _ ≫ @Scheme.descResidueField _ _ Y _ (Scheme.stalkClosedPointTo (u₀ ≫ f)) i2 = Scheme.stalkClosedPointTo (u₀ ≫ f) :=
    @Scheme.residue_descResidueField _ _ Y _ _ i2
  have h4 : Y.residue (f.base (u₀.base (IsLocalRing.closedPoint (Y.residueField y)))) ≫ f.residueFieldMap (u₀.base (IsLocalRing.closedPoint (Y.residueField y))) ≫ b = f.stalkMap (u₀.base (IsLocalRing.closedPoint (Y.residueField y))) ≫ Scheme.stalkClosedPointTo u₀ := by
    rw [Scheme.residue_residueFieldMap_assoc, hb]
  have h5 : Y.residue (f.base (u₀.base (IsLocalRing.closedPoint (Y.residueField y)))) ≫ f.residueFieldMap (u₀.base (IsLocalRing.closedPoint (Y.residueField y))) ≫ b = Y.residue (f.base (u₀.base (IsLocalRing.closedPoint (Y.residueField y)))) ≫ @Scheme.descResidueField _ _ Y _ (Scheme.stalkClosedPointTo (u₀ ≫ f)) i2 :=
    h4.trans ((Scheme.stalkClosedPointTo_comp u₀ f).symm.trans h3.symm)
  have h2 : f.residueFieldMap (u₀.base (IsLocalRing.closedPoint (Y.residueField y))) ≫ b = (Y.residueFieldCongr e).hom := by
    rw [← he]
    let _ : Epi (Y.residue (f.base (u₀.base (IsLocalRing.closedPoint (Y.residueField y))))) :=
      ConcreteCategory.epi_of_surjective _ (Y.residue_surjective _)
    apply (cancel_epi (Y.residue (f.base (u₀.base (IsLocalRing.closedPoint (Y.residueField y)))))).mp h5
  rw [ConcreteCategory.isIso_iff_bijective]
  have hcomp : Function.Bijective (f.residueFieldMap (u₀.base (IsLocalRing.closedPoint (Y.residueField y))) ≫ b) := by
    rw [h2]
    apply (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  have hbinj : Function.Injective b := b.hom.injective
  refine ⟨Function.Injective.of_comp (f := ⇑(ConcreteCategory.hom b)) ?_, fun z => ?_⟩
  · apply hcomp.1
  ·
    obtain ⟨w, hw⟩ := hcomp.2 (b z)
    exact ⟨w, hbinj hw⟩


-- created on 2026-10-20
