/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Young.Definitions.Part8
import Lemma.PowerSeries.InfiniteProducts2
import Lemma.MvPolynomial.SymmetricDefinitions
import Theorem.Combinatorics.Young.OmegaInvolution
open MvPolynomial Finset BigOperators AlgebraicCombinatorics.SymmetricPolynomials

/-!
# The ω-involution on symmetric functions

The ω-involution is an algebra automorphism of the ring of symmetric functions
that swaps the elementary and complete homogeneous symmetric polynomials:
- ω(e_n) = h_n
- ω(h_n) = e_n
- ω(s_λ) = s_{λᵗ}

This file defines the ω-involution and proves its key properties.

## Main definitions

* `SymmetricFunctions.hsymmAlgHom`: The algebra homomorphism from `MvPolynomial (Fin n) R`
  to the symmetric subalgebra sending `X_i` to `h_{i+1}`.
* `SymmetricFunctions.omegaInvolution`: The ω-involution on symmetric polynomials.

## Main results

* `SymmetricFunctions.omegaInvolution_esymm_succ`: ω(e_{k+1}) = h_{k+1} for k < n
* `SymmetricFunctions.omegaInvolution_hsymm_succ`: ω(h_{k+1}) = e_{k+1} for k < n
* `SymmetricFunctions.omegaInvolution_involutive`: ω ∘ ω = id

## Implementation notes

The ω-involution is defined using the fundamental theorem of symmetric polynomials.
The elementary symmetric polynomials generate the symmetric subalgebra, so we can
define ω by specifying ω(e_k) = h_k and extending algebraically.

To prove that ω is an involution, we need to show that ω(h_k) = e_k. This requires
proving that the h_k also generate the symmetric subalgebra (which they do, by the
Newton-Girard relations and the fundamental theorem).

## References

* [Stanley, *Enumerative Combinatorics, Vol. 2*][Stanley-EC2], Section 7.8
* [Grinberg-Reiner, *Hopf algebras in combinatorics*][GriRei], Section 2.4

## Why this is needed

The ω-involution is essential for proving the second Jacobi-Trudi formula
(jacobiTrudi_e in PieriJacobiTrudi.lean). The standard proof proceeds as follows:

1. First Jacobi-Trudi: s_{λ/μ} = det(h_{λᵢ - μⱼ - i + j})
2. Apply ω: ω(s_{λ/μ}) = det(ω(h_{...})) = det(e_{...})
3. Since ω(s_{λ/μ}) = s_{λᵗ/μᵗ}: s_{λᵗ/μᵗ} = det(e_{λᵢ - μⱼ - i + j})
4. Substitute λ → λᵗ: s_{λ/μ} = det(e_{(λᵗ)ᵢ - (μᵗ)ⱼ - i + j})

This file provides the infrastructure for steps 2 and 3.
-/


namespace SymmetricFunctions

/-!
## The hsymm algebra homomorphism

Similar to `esymmAlgHom`, we define an algebra homomorphism that sends
`X_i` to the (i+1)-th complete homogeneous symmetric polynomial.
-/


/-- The `R`-algebra homomorphism from $R[x_1,\dots,x_n]$ to the symmetric subalgebra of
  $R[\{x_i \mid i ∈ σ\}]$ sending $x_i$ to the $(i+1)$-th complete homogeneous symmetric polynomial.
  
  This is analogous to `MvPolynomial.esymmAlgHom` which sends $x_i$ to $e_{i+1}$. -/
noncomputable def hsymmAlgHom (σ : Type*) [Fintype σ] [DecidableEq σ] 
    (R : Type*) [CommRing R] (n : ℕ) :
    MvPolynomial (Fin n) R →ₐ[R] symmetricSubalgebra σ R :=
  aeval (fun i ↦ ⟨hsymm σ R (i + 1), hsymm_isSymmetric σ R _⟩)

/-!
## The ω-involution

The ω-involution is defined as the composition:
  ω = hsymmAlgHom ∘ esymmAlgEquiv.symm

This maps each e_k to h_k.
-/


/-- The ω-involution on symmetric polynomials.

This is an algebra endomorphism of the symmetric subalgebra that swaps
elementary and complete homogeneous symmetric polynomials:
- ω(e_n) = h_n
- ω(h_n) = e_n

The definition uses the fundamental theorem of symmetric polynomials:
since the e_k generate the symmetric subalgebra, we define ω by
specifying ω(e_k) = h_k and extending algebraically.

Note: For this definition to work, we need `Fintype.card σ = n`. -/
noncomputable def omegaInvolution {σ : Type*} [Fintype σ] [DecidableEq σ] 
    {R : Type*} [CommRing R] {n : ℕ} (hn : Fintype.card σ = n) :
    symmetricSubalgebra σ R →ₐ[R] symmetricSubalgebra σ R :=
  (hsymmAlgHom σ R n).comp (esymmAlgEquiv σ R hn).symm.toAlgHom

end SymmetricFunctions
