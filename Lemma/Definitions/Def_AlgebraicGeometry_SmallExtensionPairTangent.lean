import Mathlib

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

universe u

open TensorProduct IsLocalRing CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.SmallExtension

variable {T' : Type u} [CommRing T'] [IsLocalRing T'] (I : Ideal T')
  (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
  [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
  (ι : V →ₗ[T'] T')
  (C : Type u) [CommRing C] [Algebra T' C]

def pairRing : Subring (C × C) :=
  RingHom.eqLocus ((Ideal.Quotient.mk (I.map (algebraMap T' C))).comp (RingHom.fst C C))
    ((Ideal.Quotient.mk (I.map (algebraMap T' C))).comp (RingHom.snd C C))

theorem mem_pairRing {x : C × C} :
    x ∈ pairRing I C ↔ Ideal.Quotient.mk (I.map (algebraMap T' C)) x.1 = Ideal.Quotient.mk (I.map (algebraMap T' C)) x.2 :=
  Iff.rfl

def pairFst : pairRing I C →+* C := (RingHom.fst C C).comp (pairRing I C).subtype

def pairSnd : pairRing I C →+* C := (RingHom.snd C C).comp (pairRing I C).subtype

@[simp] theorem pairFst_apply (x : pairRing I C) : pairFst I C x = (x : C × C).1 := rfl
@[simp] theorem pairSnd_apply (x : pairRing I C) : pairSnd I C x = (x : C × C).2 := rfl

variable (T') in

abbrev thickening : Type u := (ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] TrivSqZeroExt (ResidueField T') V

variable (T') in

def toReduction : C →+* ResidueField T' ⊗[T'] C := Algebra.TensorProduct.includeRight.toRingHom

def IsSchlessingerMap (ϑ : pairRing I C →+* thickening T' V C) : Prop :=
  (∀ (a : C) (ha : (a, a) ∈ pairRing I C), ϑ ⟨(a, a), ha⟩ = toReduction T' C a ⊗ₜ (1 : TrivSqZeroExt (ResidueField T') V)) ∧
  (∀ (v : V) (c : C) (h : ((0 : C), algebraMap T' C (ι v) * c) ∈ pairRing I C),
    ϑ ⟨((0 : C), algebraMap T' C (ι v) * c), h⟩ = toReduction T' C c ⊗ₜ TrivSqZeroExt.inr v)

def IsTangentOfPair {Y : Scheme.{u}} (u v : Spec (CommRingCat.of C) ⟶ Y)
    (w : Spec (CommRingCat.of (thickening T' V C)) ⟶ Y) : Prop :=
  ∃ (ϑ : pairRing I C →+* thickening T' V C) (_ : IsSchlessingerMap I V ι C ϑ)
    (φ : Spec (CommRingCat.of (pairRing I C)) ⟶ Y),
    Spec.map (CommRingCat.ofHom (pairFst I C)) ≫ φ = u ∧
    Spec.map (CommRingCat.ofHom (pairSnd I C)) ≫ φ = v ∧
    w = Spec.map (CommRingCat.ofHom ϑ) ≫ φ

end AlgebraicGeometry.SmallExtension

end
