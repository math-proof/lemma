import Mathlib

set_option autoImplicit false

namespace AlgebraicGeometry.HilbertFunctor

open MvPolynomial

variable {A : Type*} [CommRing A] {n : ℕ}

abbrev piece (I : Ideal (MvPolynomial (Fin (n + 1)) A)) (d : ℕ) : Type _ :=
  ↥(homogeneousSubmodule (Fin (n + 1)) A d) ⧸
    Submodule.comap (homogeneousSubmodule (Fin (n + 1)) A d).subtype (I.restrictScalars A)

variable (A n)

structure Point (h : ℕ → ℕ) where

  I : Ideal (MvPolynomial (Fin (n + 1)) A)

  homogeneous : ∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I

  finite_piece : ∀ d : ℕ, Module.Finite A (piece I d)

  projective_piece : ∀ d : ℕ, Module.Projective A (piece I d)

  rankAtStalk_piece : ∀ (d : ℕ) (p : PrimeSpectrum A), Module.rankAtStalk (piece I d) p = h d

variable {A}

@[ext] theorem Point.ext {h : ℕ → ℕ} {P Q : Point A n h} (e : P.I = Q.I) : P = Q := by
  cases P; cases Q; cases e; rfl

noncomputable def hilbertFunctionOf (P : Polynomial ℚ) (D₀ : ℕ) : ℕ → ℕ :=
  fun d => if d < D₀ then Nat.choose (n + d) n else Int.toNat ⌊P.eval (d : ℚ)⌋

end AlgebraicGeometry.HilbertFunctor
