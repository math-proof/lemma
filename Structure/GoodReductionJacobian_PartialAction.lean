import Mathlib
import Structure.AlgebraicGeometry_RelativeGroupLaw
import Lemma.AlgebraicGeometry.NeronModelEndomorphismExtension

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian

structure PartialAction (k : Type u) [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) where

  dom : (pullback f p).Opens

  dense_dom : Dense (dom : Set ↥(pullback f p))

  hom : (dom : Scheme.{u}) ⟶ P

  hom_comp : hom ≫ p = dom.ι ≫ pullback.snd f p ≫ p

namespace PartialAction

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  {P : Scheme.{u}} {p : P ⟶ Spec (CommRingCat.of k)}


end PartialAction

end GoodReductionJacobian

end
