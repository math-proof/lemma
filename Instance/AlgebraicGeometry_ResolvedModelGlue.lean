-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_ResolvedModelGlue.lean: instance decls only.
import Mathlib
import Lemma.AlgebraicGeometry.ResolvedModelGlue

set_option autoImplicit false
set_option maxHeartbeats 200000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace V3Glue


namespace GlueInput

variable {X : Scheme.{0}} {N : Type} (D : GlueInput X N)

instance F₁_isOpenImmersion (n : N) {i k : WidePushoutShape Bool} (f : i ⟶ k) :
    IsOpenImmersion ((D.F₁ n).map f) := by
  obtain - | b := f
  · change IsOpenImmersion (𝟙 _); infer_instance
  · cases b
    · change IsOpenImmersion (D.j n); infer_instance
    · change IsOpenImmersion (X.homOfLE (inf_le_right : D.U n ⊓ D.X0 ≤ D.X0)); infer_instance

instance (n : N) : IsOpenImmersion (D.ιX0'' n) :=
  inferInstanceAs (IsOpenImmersion ((Scheme.IsLocallyDirected.openCover (D.F₁ n)).f (some true)))
instance (n : N) : IsOpenImmersion (D.ιY'' n) :=
  inferInstanceAs (IsOpenImmersion ((Scheme.IsLocallyDirected.openCover (D.F₁ n)).f (some false)))

instance F₂_isOpenImmersion {i k : WidePushoutShape N} (f : i ⟶ k) : IsOpenImmersion (D.F₂.map f) := by
  obtain - | n := f
  · change IsOpenImmersion (𝟙 _); infer_instance
  · change IsOpenImmersion (D.ιX0'' n); infer_instance

instance : IsOpenImmersion D.ιX0 :=
  inferInstanceAs (IsOpenImmersion ((Scheme.IsLocallyDirected.openCover D.F₂).f none))
instance (n : N) : IsOpenImmersion (D.ιY''glued n) :=
  inferInstanceAs (IsOpenImmersion ((Scheme.IsLocallyDirected.openCover D.F₂).f (some n)))
instance (n : N) : IsOpenImmersion (D.ιY n) := by dsimp [ιY]; infer_instance

variable (hq : ∀ n (y : D.Y n), ((D.q n).base y).1 ∈ D.X0 → y ∈ Set.range (D.j n).base)

end GlueInput

end V3Glue

namespace V3Glue


namespace ChartInput

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)

instance f_flat (n : N) : Flat (C.f n) := ((Etale.iff_flat_and_formallyUnramified).mp (C.f_etale n)).1

instance f_lfp (n : N) : LocallyOfFinitePresentation (C.f n) := ((Etale.iff_flat_and_formallyUnramified).mp (C.f_etale n)).2.2

instance (n : N) : IsProper (C.q n) :=
  MorphismProperty.pullback_fst _ _ inferInstance

instance isIso_pullback_fst_ι_ρ (n : N) : IsIso (pullback.fst (C.Vc n).ι (C.ρ n)) := by
  have : IsIso (pullback.snd (C.ρ n) (C.Vc n).ι) := by
    rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict]
    infer_instance
  have : pullback.fst (C.Vc n).ι (C.ρ n) = (pullbackSymmetry _ _).hom ≫ pullback.snd (C.ρ n) (C.Vc n).ι :=
    (pullbackSymmetry_hom_comp_snd _ _).symm
  rw [this]; infer_instance

instance isIso_pullback_fst_a_q (n : N) : IsIso (pullback.fst (C.a n) (C.q n)) := by

  let e₁ : pullback (C.a n) (C.q n) ≅ pullback (C.a n ≫ C.f n) (C.ρ n) :=
    pullbackRightPullbackFstIso (C.f n) (C.ρ n) (C.a n)
  let e₂ : pullback (C.a n ≫ C.f n) (C.ρ n) ≅ pullback (C.l n ≫ (C.Vc n).ι) (C.ρ n) :=
    pullback.congrHom (C.l_ι n).symm rfl
  let e₃ : pullback (C.l n ≫ (C.Vc n).ι) (C.ρ n) ≅ pullback (C.l n) (pullback.fst (C.Vc n).ι (C.ρ n)) :=
    (pullbackRightPullbackFstIso ((C.Vc n).ι) (C.ρ n) (C.l n)).symm
  have h3 : pullback.fst (C.l n ≫ (C.Vc n).ι) (C.ρ n) =
      e₃.hom ≫ pullback.fst (C.l n) (pullback.fst (C.Vc n).ι (C.ρ n)) := by
    simp only [e₃, Iso.symm_hom, pullbackRightPullbackFstIso_inv_fst]
  have h2 : pullback.fst (C.a n ≫ C.f n) (C.ρ n) = e₂.hom ≫ pullback.fst (C.l n ≫ (C.Vc n).ι) (C.ρ n) := by
    simp only [e₂, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id]
  have h1 : pullback.fst (C.a n) (C.q n) = e₁.hom ≫ pullback.fst (C.a n ≫ C.f n) (C.ρ n) := by
    simp only [e₁, q]
    exact (pullbackRightPullbackFstIso_hom_fst _ _ _).symm
  rw [h1, h2, h3]
  infer_instance

instance (n : N) : IsOpenImmersion (C.j n) := by
  dsimp [j]; infer_instance

instance (n : N) : Flat (C.g n) := MorphismProperty.pullback_snd _ _ inferInstance
instance (n : N) : LocallyOfFinitePresentation (C.g n) := MorphismProperty.pullback_snd _ _ inferInstance

instance isLocallyNoetherian_Y (n : N) : IsLocallyNoetherian (C.Y n) :=
  LocallyOfFiniteType.isLocallyNoetherian (C.g n)

instance flat_toB (n : N) : Flat (C.toB n) := by
  dsimp [toB]; infer_instance

end ChartInput


end V3Glue

end


