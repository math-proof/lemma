import Mathlib
import Lemma.Definitions.Def_FreyPackage_GaloisRep

set_option autoImplicit false

namespace WeierstrassCurve.Affine.Point

open WeierstrassCurve

universe r s v

variable {R : Type r} {S : Type s} {K : Type v} [CommRing R] [CommRing S] [Field K]
  [DecidableEq K] {W' : Affine R} [Algebra R S] [Algebra R K] [Algebra S K]
  [IsScalarTower R S K]

variable (S) in

structure IsWeilPairing (W' : Affine R) (n : ℕ)
    (B : Submodule.torsionBy ℤ (W'⁄K).Point n → Submodule.torsionBy ℤ (W'⁄K).Point n → Kˣ) :
    Prop where

  mem_rootsOfUnity : ∀ P Q, B P Q ∈ rootsOfUnity n K

  add_left : ∀ P P' Q, B (P + P') Q = B P Q * B P' Q

  add_right : ∀ P Q Q', B P (Q + Q') = B P Q * B P Q'

  alternate : ∀ P, B P P = 1

  equivariant : ∀ (σ : K ≃ₐ[S] K) (P Q), σ ((B P Q : Kˣ) : K) = ((B (σ • P) (σ • Q) : Kˣ) : K)

  nondegenerate : ∃ P Q, B P Q ≠ 1

variable (S K) in

def HasWeilPairing (W' : Affine R) (n : ℕ) : Prop :=
  ∃ B : Submodule.torsionBy ℤ (W'⁄K).Point n → Submodule.torsionBy ℤ (W'⁄K).Point n → Kˣ,
    IsWeilPairing S W' n B

end WeierstrassCurve.Affine.Point
