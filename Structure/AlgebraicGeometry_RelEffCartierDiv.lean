module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Structure.AlgebraicCurve_UniversalDivisor

public section

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
