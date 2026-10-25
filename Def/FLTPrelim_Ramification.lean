import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.RingTheory.Valuation.ValuationSubring
import Lemma.FLTPrelim.FreyPackage
import Instance.FLTPrelim_GaloisRep

set_option autoImplicit false

noncomputable section

universe u

namespace ValuationSubring

variable {L : Type u} [Field L]

def LiesOverPrime (A : ValuationSubring L) (q : ℕ) : Prop :=
  (q : L) ∈ A.nonunits

variable (K : Type*) [Field K] [Algebra K L]

def inertiaSubgroupIn (A : ValuationSubring L) : Subgroup (L ≃ₐ[K] L) :=
  (A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype

end ValuationSubring

namespace WeierstrassCurve.Affine.Point

open WeierstrassCurve

variable {R : Type*} {S : Type*} {K : Type*} [CommRing R] [Field S] [Field K]
  [DecidableEq K] [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K]

variable (S K) in

def GaloisRepUnramifiedAt (W' : Affine R) (n : ℕ) (q : ℕ) : Prop :=
  ∀ A : ValuationSubring K, A.LiesOverPrime q →
    ∀ σ ∈ A.inertiaSubgroupIn S,
    ∀ x : Submodule.torsionBy ℤ (W'⁄K).Point n, σ • x = x

end WeierstrassCurve.Affine.Point

namespace FreyPackage

open WeierstrassCurve.Affine.Point

def GaloisRepUnramifiedAt (P : FreyPackage) (q : ℕ) : Prop :=
  WeierstrassCurve.Affine.Point.GaloisRepUnramifiedAt (K := AlgebraicClosure ℚ) ℚ
    P.freyCurve P.p q

end FreyPackage

end
