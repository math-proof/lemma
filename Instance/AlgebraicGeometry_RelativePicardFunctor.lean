-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_RelativePicardFunctor.lean: instance decls only.
import Mathlib
import Lemma.AlgebraicGeometry.NeronModelPropertyBundleCarrier
import Def.AlgebraicGeometry_RelativePicardFunctor

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open NeronModelInfra

noncomputable section

namespace AlgebraicGeometry

instance Scheme.Hom.opensMapFinal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (TopologicalSpace.Opens.map f.base).Final :=
  CategoryTheory.final_of_representablyFlat _

namespace RelPicard

variable {R : Type u} [CommRing R]

namespace RigidifiedLineBundle

variable {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}

instance {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    Inhabited (RigidifiedLineBundle c ε t) := ⟨unit t⟩

instance setoid {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    Setoid (RigidifiedLineBundle c ε t) where
  r M M' := Nonempty (M.L ≅ M'.L)
  iseqv := ⟨fun _ => ⟨Iso.refl _⟩, fun ⟨i⟩ => ⟨i.symm⟩, fun ⟨i⟩ ⟨j⟩ => ⟨i ≪≫ j⟩⟩

end RigidifiedLineBundle

end RelPicard

end AlgebraicGeometry

end
