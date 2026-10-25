import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Structure.AlgebraicCurve_UniversalDivisor

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

structure RelEffCartierDiv {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) (r : ℕ)
    {T : Scheme.{u}} (g : T ⟶ S) where

  I : (pullback f g).IdealSheafData

  isFinite : IsFinite (I.subschemeι ≫ pullback.snd f g)

  flat : Flat (I.subschemeι ≫ pullback.snd f g)

  locallyOfFinitePresentation : LocallyOfFinitePresentation (I.subschemeι ≫ pullback.snd f g)

  finrank_eq : ∀ t : T, (I.subschemeι ≫ pullback.snd f g).finrank t = r


section transport

variable {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {T T' : Scheme.{u}} {g : T ⟶ S} {g' : T' ⟶ S}


end transport


section FieldComparison

variable {k : Type u} [Field k]


end FieldComparison

end AlgebraicGeometry
