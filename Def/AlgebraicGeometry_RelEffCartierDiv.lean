module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Def.AlgebraicCurve_UniversalDivisor
public import Structure.AlgebraicGeometry_RelEffCartierDiv

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry


noncomputable def mapOnProdOver {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S)
    {T T' : Scheme.{u}} {g : T ⟶ S} {g' : T' ⟶ S} (φ : T ⟶ T') (hφ : φ ≫ g' = g) :
    pullback f g ⟶ pullback f g' :=
  pullback.map f g f g' (𝟙 𝒞) φ (𝟙 S) (by simp) (by rw [Category.comp_id, hφ])

def PullsBackOver {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ}
    {T' : Scheme.{u}} {g' : T' ⟶ S} (D : RelEffCartierDiv f r g')
    {T : Scheme.{u}} {g : T ⟶ S} (φ : T ⟶ T') (hφ : φ ≫ g' = g)
    (D' : RelEffCartierDiv f r g) : Prop :=
  D.I.comap (mapOnProdOver f φ hφ) = D'.I

section transport

variable {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {T T' : Scheme.{u}} {g : T ⟶ S} {g' : T' ⟶ S}

noncomputable def comapSubschemeMapOver (I : (pullback f g').IdealSheafData) (φ : T ⟶ T')
    (hφ : φ ≫ g' = g) : (I.comap (mapOnProdOver f φ hφ)).subscheme ⟶ I.subscheme :=
  (I.comapIso (mapOnProdOver f φ hφ)).hom ≫ pullback.snd _ _

end transport

noncomputable def RelEffCartierDiv.pullbackAlong {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ}
    {T' : Scheme.{u}} {g' : T' ⟶ S} (D : RelEffCartierDiv f r g')
    {T : Scheme.{u}} {g : T ⟶ S} (φ : T ⟶ T') (hφ : φ ≫ g' = g) : RelEffCartierDiv f r g where
  I := D.I.comap (mapOnProdOver f φ hφ)
  isFinite :=
    have := D.isFinite
    MorphismProperty.of_isPullback (isPullback_comap_snd_over D.I φ hφ) ‹_›
  flat :=
    have := D.flat
    MorphismProperty.of_isPullback (isPullback_comap_snd_over D.I φ hφ) ‹_›
  locallyOfFinitePresentation :=
    have := D.locallyOfFinitePresentation
    MorphismProperty.of_isPullback (isPullback_comap_snd_over D.I φ hφ) ‹_›
  finrank_eq t := by
    have := D.isFinite
    have := D.flat
    have := D.locallyOfFinitePresentation
    rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ (isPullback_comap_snd_over D.I φ hφ) t]
    exact D.finrank_eq (φ t)

section FieldComparison

variable {k : Type u} [Field k]

def RelEffCartierDiv.toRelEffDivisor {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)}
    {r : ℕ} {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (D : RelEffCartierDiv c r t) :
    AlgebraicCurve.RelEffDivisor C c r T t :=
  ⟨D.I, D.isFinite, D.flat, D.finrank_eq⟩

def RelEffCartierDiv.ofRelEffDivisor {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)}
    {r : ℕ} {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    (D : AlgebraicCurve.RelEffDivisor C c r T t)
    (h : LocallyOfFinitePresentation (D.I.subschemeι ≫ pullback.snd c t)) :
    RelEffCartierDiv c r t :=
  ⟨D.I, D.isFinite, D.flat, h, D.finrank_eq⟩

end FieldComparison

end AlgebraicGeometry

end
