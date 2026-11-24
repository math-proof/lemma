module
public import Mathlib
public import Instance.AlgebraicGeometry_RelativePicardFunctor
public import Theorem.Scheme.PolarisationRosati
public import Abbrev.GoodReductionJacobian_RelativeGroupLawBaseChange
public import Theorem.Scheme.SymmRootFunctor
set_option autoImplicit false


public section

-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_SymmRootFunctor.lean: instance decls only.

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

namespace AlgebraicGeometry.SymmRoot


section functor
variable {S : Type u} [CommRing S] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of S))

variable (P : StablePred c ε R₀)

instance setoid (B : Under (CommRingCat.of R₀)) : Setoid (Elem c ε R₀ P B) where
  r x y := Nonempty (x.M.L ≅ y.M.L)
  iseqv := ⟨fun _ => ⟨Iso.refl _⟩, fun ⟨i⟩ => ⟨i.symm⟩, fun ⟨i⟩ ⟨j⟩ => ⟨i ≪≫ j⟩⟩

end functor


end AlgebraicGeometry.SymmRoot

end
