import Lemma.ModularCurve.CharLDegeneracyHecke
import Def.ModularCurve_PlaceWidth
import Def.CerednikDrinfeld_Ribbon
import Structure.ModularCurve_SSDegeneracyHecke

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace ModularCurve

section LevelLegs

variable (K : Type*) [Field K] (M s : ℕ) [NeZero M] [NeZero s]


theorem coe_levelAlphaC (hM : jqNModC K M ∈ modularFunctionFieldC K (M * s)) (x : modularFunctionFieldC K M) :
    (levelAlphaC K M s hM x : LaurentSeries K) = (x : LaurentSeries K) :=
  IntermediateField.coe_inclusion _ x


theorem coe_levelBetaC (hS : jqNModC K s ∈ modularFunctionFieldC K (M * s)) (x : modularFunctionFieldC K M) :
    (levelBetaC K M s hS x : LaurentSeries K) = qExpand K s (x : LaurentSeries K) :=
  rfl


end LevelLegs

section Matrices

variable (p : ℕ) (K : Type*) [Field K] [DecidableEq K] (N : ℕ) [NeZero N]

open Classical in

def ssHeckeMatrixC (ℓ : ℕ) [NeZero ℓ] (hα : (heckeAlphaC K N ℓ).toRingHom.IsIntegral)
    (hβ : (heckeBetaC K N ℓ).toRingHom.IsIntegral) : Matrix ↥(ssPlaces p N K) ↥(ssPlaces p N K) ℤ :=
  Matrix.of fun y x =>
    ∑ᶠ W : Place K (charLDegeneracyRoof K N ℓ),
      if Place.restrictAlong (heckeBetaC K N ℓ) hβ W = x.1 ∧ Place.restrictAlong (heckeAlphaC K N ℓ) hα W = y.1 then
        (Place.ramificationIndexAlong (heckeBetaC K N ℓ) W : ℤ) * (Place.inertiaDegAlong (heckeAlphaC K N ℓ) hα W : ℤ)
      else 0

variable [Fact p.Prime] [CharP K p]

open Classical in

def ssFrobMatrixC (data : ModularPolynomialData p) (hKr : KroneckerCongruence p data) :
    Matrix ↥(ssPlaces p N K) ↥(ssPlaces p N K) ℤ :=
  Matrix.of fun y x => if frobOnPlacesGeomLevel K N data hKr x.1 = y.1 then 1 else 0

def ssHeckeFamilyC (data : ModularPolynomialData p) (hKr : KroneckerCongruence p data)
    (hlegs : ∀ (ℓ : ℕ) [NeZero ℓ], (heckeAlphaC K N ℓ).toRingHom.IsIntegral ∧ (heckeBetaC K N ℓ).toRingHom.IsIntegral)
    (ℓ : Nat.Primes) : Matrix ↥(ssPlaces p N K) ↥(ssPlaces p N K) ℤ :=
  letI : NeZero (ℓ : ℕ) := ⟨ℓ.2.pos.ne'⟩
  if (ℓ : ℕ) = p then ssFrobMatrixC p K N data hKr else ssHeckeMatrixC p K N ℓ (hlegs ℓ).1 (hlegs ℓ).2

end Matrices

section Datum

variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p] [DecidableEq K] (M s : ℕ) [NeZero M] [NeZero s]


namespace SSLevelDatum

variable {p K M s}
variable (X : SSLevelDatum p K M s)

def fst (W : ↥(ssPlaces p (M * s) K)) : ↥(ssPlaces p M K) :=
  ⟨Place.restrictAlong (levelAlphaC K M s X.mem_M) X.fstIntegral W.1, X.fst_mem W.1 W.2⟩

def snd (W : ↥(ssPlaces p (M * s) K)) : ↥(ssPlaces p M K) :=
  ⟨Place.restrictAlong (levelBetaC K M s X.mem_s) X.sndIntegral W.1, X.snd_mem W.1 W.2⟩

def atkinLehnerPerm (W : ↥(ssPlaces p (M * s) K)) : ↥(ssPlaces p (M * s) K) :=
  ⟨autOnPlaces K M s X.atkinLehnerAut W.1, X.stable W.1 W.2⟩

def degeneracyData : CerednikDrinfeld.DegeneracyData ↥(ssPlaces p (M * s) K) ↥(ssPlaces p M K) where
  a := X.fst
  b := X.snd
  w W := Nat.toPNat' (placeWidth (M * s) W.1)

def edgeHecke : Nat.Primes → Matrix ↥(ssPlaces p (M * s) K) ↥(ssPlaces p (M * s) K) ℤ :=
  ssHeckeFamilyC p K (M * s) X.frobData X.kronecker (X.legsIntegral (M * s))

def vertexHecke : Nat.Primes → Matrix ↥(ssPlaces p M K) ↥(ssPlaces p M K) ℤ :=
  ssHeckeFamilyC p K M X.frobData X.kronecker (X.legsIntegral M)

section Laws

variable [Fact s.Prime] [Fintype ↥(ssPlaces p (M * s) K)] [Fintype ↥(ssPlaces p M K)] [DecidableEq ↥(ssPlaces p M K)]

def HeckeLaws : Prop :=
  (∀ ℓ ℓ' : Nat.Primes, Commute (X.edgeHecke ℓ) (X.edgeHecke ℓ')) ∧
  (∀ ℓ ℓ' : Nat.Primes, Commute (X.vertexHecke ℓ) (X.vertexHecke ℓ')) ∧
  (∀ ℓ : Nat.Primes, ℓ ∉ ({⟨s, Fact.out⟩} : Finset Nat.Primes) → ∀ i : Fin 2,
    ∀ x : ↥(ssPlaces p (M * s) K) → ℤ,
      CerednikDrinfeld.jointDelta X.degeneracyData i ((X.edgeHecke ℓ).mulVecLin x) =
        (X.vertexHecke ℓ).mulVecLin (CerednikDrinfeld.jointDelta X.degeneracyData i x)) ∧
  (∀ ℓ : Nat.Primes, ∀ x : ↥(ssPlaces p (M * s) K) → ℤ,
    (∀ i, CerednikDrinfeld.jointDelta X.degeneracyData i x = 0) →
      ∀ i, CerednikDrinfeld.jointDelta X.degeneracyData i ((X.edgeHecke ℓ).mulVecLin x) = 0)

open Classical in

def heckeData : CerednikDrinfeld.HeckeData X.degeneracyData :=
  if h : X.HeckeLaws then
    { T := X.edgeHecke
      Tv := X.vertexHecke
      comm := h.1
      commv := h.2.1
      S := {⟨s, Fact.out⟩}
      good_equivariant := h.2.2.1
      kernel_stable := h.2.2.2 }
  else
    { T := 0
      Tv := 0
      comm := fun _ _ => Commute.refl 0
      commv := fun _ _ => Commute.refl 0
      S := {⟨s, Fact.out⟩}
      good_equivariant := fun _ _ i x => by
        simp only [Pi.zero_apply, LinearMap.zero_apply, map_zero]
      kernel_stable := fun _ x _ i => by
        simp only [Pi.zero_apply, LinearMap.zero_apply, map_zero] }

end Laws

end SSLevelDatum

end Datum

end ModularCurve

end
