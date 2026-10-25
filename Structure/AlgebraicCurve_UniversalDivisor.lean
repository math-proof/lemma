import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Properties

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicCurve

variable {k : Type u} [Field k]

structure RelEffDivisor (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of k)) (r : ℕ)
    (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of k)) where
  I : (pullback c t).IdealSheafData
  isFinite : IsFinite (I.subschemeι ≫ pullback.snd c t)
  flat : Flat (I.subschemeι ≫ pullback.snd c t)
  finrank_eq : ∀ s : T, (I.subschemeι ≫ pullback.snd c t).finrank s = r


noncomputable def mapOnProd {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    {T Csym : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    {csym : Csym ⟶ Spec (CommRingCat.of k)} (φ : T ⟶ Csym) (hφ : φ ≫ csym = t) :
    pullback c t ⟶ pullback c csym :=
  pullback.map c t c csym (𝟙 C) φ (𝟙 (Spec (CommRingCat.of k))) (by simp)
    (by rw [Category.comp_id, hφ])

@[reassoc (attr := simp)]


def PullsBack {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)} {r : ℕ}
    {Csym : Scheme.{u}} {csym : Csym ⟶ Spec (CommRingCat.of k)}
    (Dcan : RelEffDivisor C c r Csym csym)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (φ : T ⟶ Csym)
    (hφ : φ ≫ csym = t) (D' : RelEffDivisor C c r T t) : Prop :=
  Dcan.I.comap (mapOnProd c φ hφ) = D'.I

section transport

variable {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)}
    {Csym : Scheme.{u}} {csym : Csym ⟶ Spec (CommRingCat.of k)}
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}


end transport


structure UnivDivisorPack (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of k)) (r : ℕ)
    (Csym : Scheme.{u}) (csym : Csym ⟶ Spec (CommRingCat.of k)) where
  Dcan : RelEffDivisor C c r Csym csym
  exists_pullsBack : ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of k)) [IsIntegral T]
    [LocallyOfFiniteType t] [QuasiCompact t] (D' : RelEffDivisor C c r T t),
    ∃ (φ : T ⟶ Csym) (hφ : φ ≫ csym = t), PullsBack Dcan φ hφ D'
  eq_of_pullsBack : ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of k)) [IsReduced T]
    [LocallyOfFiniteType t] [QuasiCompact t] (D' : RelEffDivisor C c r T t)
    (φ₁ φ₂ : T ⟶ Csym) (hφ₁ : φ₁ ≫ csym = t) (hφ₂ : φ₂ ≫ csym = t),
    PullsBack Dcan φ₁ hφ₁ D' → PullsBack Dcan φ₂ hφ₂ D' → φ₁ = φ₂

end AlgebraicCurve
