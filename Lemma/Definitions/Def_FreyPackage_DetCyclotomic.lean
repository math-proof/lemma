import Lemma.Definitions.Def_FreyPackage_GaloisRep
import Lemma.Definitions.Def_FLTPrelim_Ramification
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.LinearAlgebra.Determinant
import Lemma.Definitions.Def_ExtCitation_AdmissibleExtension

set_option autoImplicit false

universe r s v

namespace WeierstrassCurve.Affine.Point

open WeierstrassCurve

variable {R : Type r} {S : Type s} {K : Type v} [CommRing R] [CommRing S] [Field K]
  [DecidableEq K] {W' : Affine R} [Algebra R S] [Algebra R K] [Algebra S K]
  [IsScalarTower R S K]

noncomputable def galoisRepDet (W' : Affine R) (n : ℕ) : (K ≃ₐ[S] K) →* (ZMod n)ˣ :=
  LinearEquiv.det.comp (galoisRep (S := S) (K := K) W' n)

@[simp]
lemma galoisRepDet_apply (n : ℕ) (σ : K ≃ₐ[S] K) :
    galoisRepDet (S := S) (K := K) W' n σ = LinearEquiv.det (galoisRep (S := S) W' n σ) :=
  rfl

variable (S) in

def GaloisRepDetEqCyclotomic (W' : Affine R) (n : ℕ) [NeZero n]
    (hn : Nat.card (rootsOfUnity n K) = n) : Prop :=
  ∀ σ : K ≃ₐ[S] K, galoisRepDet (S := S) (K := K) W' n σ =
    modularCyclotomicCharacter K hn (σ : K ≃+* K)

theorem galoisRepDetEqCyclotomic_two (hn : Nat.card (rootsOfUnity 2 K) = 2) :
    GaloisRepDetEqCyclotomic S W' 2 hn := fun _ => Subsingleton.elim _ _

end WeierstrassCurve.Affine.Point

section AlgClosed

end AlgClosed

namespace FreyPackage

open WeierstrassCurve.Affine.Point
open scoped WeierstrassCurve.Affine

noncomputable local instance instDecEqQbarDetCyclotomic : DecidableEq (AlgebraicClosure ℚ) :=
  Classical.decEq _

theorem card_rootsOfUnity_algebraicClosure (P : FreyPackage) :
    haveI : NeZero P.p := ⟨P.pp.ne_zero⟩
    Nat.card (rootsOfUnity P.p (AlgebraicClosure ℚ)) = P.p :=
  haveI : NeZero P.p := ⟨P.pp.ne_zero⟩
  IsAlgClosed.card_rootsOfUnity_eq (AlgebraicClosure ℚ) P.p

variable (P : FreyPackage)

def MuLineCyclotomicAtP : Prop :=
  haveI : NeZero P.p := ⟨P.pp.ne_zero⟩
  ∃ A₀ : ValuationSubring (AlgebraicClosure ℚ), A₀.LiesOverPrime P.p ∧
    ∃ z : Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p, z ≠ 0 ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A₀.inertiaSubgroupIn ℚ →
        (σ • z = ((modularCyclotomicCharacter (AlgebraicClosure ℚ)
            P.card_rootsOfUnity_algebraicClosure
            (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) : (ZMod P.p)ˣ) : ZMod P.p) • z) ∧
        ∀ y : Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p,
          σ • y - y ∈ Submodule.span (ZMod P.p) {z}

def DetCyclotomicOnInertiaAtP : Prop :=
  haveI : NeZero P.p := ⟨P.pp.ne_zero⟩
  ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime P.p →
    ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
      galoisRepDet (S := ℚ) (K := AlgebraicClosure ℚ) P.freyCurve P.p σ =
        modularCyclotomicCharacter (AlgebraicClosure ℚ) P.card_rootsOfUnity_algebraicClosure
          (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ)

end FreyPackage
