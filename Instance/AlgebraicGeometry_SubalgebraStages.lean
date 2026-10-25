-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_SubalgebraStages.lean: instance decls only.
import Mathlib

set_option autoImplicit false

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits Opposite

namespace SubalgebraStages

variable {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
variable {ι : Type u} [Preorder ι] (S : ι →o Subalgebra A₀ A)


instance isAffineHom_trans {i j : ι} (h : i ≤ j) : IsAffineHom (trans S f h) :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) (isPullback_trans S f h).flip inferInstance

instance isAffineHom_diagram_map {i j : ιᵒᵖ} (h : i ⟶ j) : IsAffineHom ((diagram S f).map h) :=
  isAffineHom_trans S f h.unop.le

instance isAffineHom_leg (i : ι) : IsAffineHom (leg S f i) :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) (isPullback_leg S f i).flip inferInstance

instance quasiCompact_snd [QuasiCompact f] (i : ι) : QuasiCompact (pullback.snd f (specHom S i)) :=
  MorphismProperty.pullback_snd (P := @QuasiCompact) _ _ inferInstance

instance quasiSeparated_snd [QuasiSeparated f] (i : ι) : QuasiSeparated (pullback.snd f (specHom S i)) :=
  MorphismProperty.pullback_snd (P := @QuasiSeparated) _ _ inferInstance

instance compactSpace_pullback [QuasiCompact f] (i : ι) : CompactSpace ↥(pullback f (specHom S i)) :=
  @QuasiCompact.compactSpace_of_compactSpace _ _ (pullback.snd f (specHom S i)) (quasiCompact_snd S f i)
    (inferInstance : CompactSpace (PrimeSpectrum ↥(S i)))

instance compactSpace_obj [QuasiCompact f] (i : ιᵒᵖ) : CompactSpace ↥((diagram S f).obj i) :=
  compactSpace_pullback S f i.unop

instance quasiSeparatedSpace_pullback [QuasiSeparated f] (i : ι) : QuasiSeparatedSpace ↥(pullback f (specHom S i)) :=
  @quasiSeparatedSpace_of_quasiSeparated _ _ (pullback.snd f (specHom S i)) inferInstance (quasiSeparated_snd S f i)

instance quasiSeparatedSpace_obj [QuasiSeparated f] (i : ιᵒᵖ) : QuasiSeparatedSpace ↥((diagram S f).obj i) :=
  quasiSeparatedSpace_pullback S f i.unop

instance isCofiltered_op [IsDirected ι (· ≤ ·)] [Nonempty ι] : IsCofiltered ιᵒᵖ := inferInstance

end SubalgebraStages

end AlgebraicGeometry
