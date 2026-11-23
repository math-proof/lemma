module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Properties
public import Structure.AlgebraicCurve_UniversalDivisor

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicCurve

variable {k : Type u} [Field k]


section transport

variable {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)}
    {Csym : Scheme.{u}} {csym : Csym ⟶ Spec (CommRingCat.of k)}
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}

noncomputable def comapSubschemeMap (I : (pullback c csym).IdealSheafData) (φ : T ⟶ Csym)
    (hφ : φ ≫ csym = t) : (I.comap (mapOnProd c φ hφ)).subscheme ⟶ I.subscheme :=
  (I.comapIso (mapOnProd c φ hφ)).hom ≫ pullback.snd _ _

end transport

noncomputable def RelEffDivisor.pullbackAlong {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of k)} {r : ℕ}
    {Csym : Scheme.{u}} {csym : Csym ⟶ Spec (CommRingCat.of k)}
    (Dcan : RelEffDivisor C c r Csym csym)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (φ : T ⟶ Csym)
    (hφ : φ ≫ csym = t) : RelEffDivisor C c r T t where
  I := Dcan.I.comap (mapOnProd c φ hφ)
  isFinite :=
    have := Dcan.isFinite
    MorphismProperty.of_isPullback (isPullback_comap_snd Dcan.I φ hφ) ‹_›
  flat :=
    have := Dcan.flat
    MorphismProperty.of_isPullback (isPullback_comap_snd Dcan.I φ hφ) ‹_›
  finrank_eq s := by
    have := Dcan.isFinite
    have := Dcan.flat
    rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ (isPullback_comap_snd Dcan.I φ hφ) s]
    exact Dcan.finrank_eq (φ s)

end AlgebraicCurve

end
