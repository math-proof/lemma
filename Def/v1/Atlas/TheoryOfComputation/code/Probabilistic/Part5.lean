/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Probabilistic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Algebra.Polynomial.Roots
import Def.v1.Atlas.TheoryOfComputation.code.BPP.Part3
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Algebra.Order.Archimedean.Basic
import Structure.v1.Atlas.TheoryOfComputation.code.Probabilistic.Part5


namespace Probabilistic

/-- The language of equivalent read-once branching programs:

`EQ_ROBP = {⟨B₁, B₂⟩ ∣ B₁ ≡ B₂ as ROBPs}`,

with the pair encoded as a string over `Γ` using `enc`. Membership in BPP is
proved in `EQ_ROBP_in_BPP`. -/
def EQ_ROBP {Γ : Type} (enc : ROBPPairEncoding Γ) : Set (List Γ) :=
  {s | ∃ d : ROBPPairDesc, enc.encode d = s ∧ d.isEquivalent}

/-- Number of random bits used by the `EQ_ROBP` BPP decider on inputs of
length `n`: a polynomial budget of `n² + 1` bits, enough to sample a random
field element per variable. -/
def eqROBP_numBits (n : ℕ) : ℕ := n ^ 2 + 1

/-- **Soundness bound for the `EQ_ROBP` randomized decider.** On a no-instance
`(B₁, B₂)` (with `B₁ ≢ B₂`), the probability that the verifier accepts is at
most `1/3`. This is the Schwartz-Zippel-based bound from Sipser Lecture 24:
when the arithmetizations `p₁, p₂` (each of total degree `≤ numVars` in every
variable) disagree, `Pr[p₁(r) = p₂(r)] ≤ d·m/q ≤ 1/3` for `q ≥ 3·numVars`. -/
noncomputable def edgeFactor {m : ℕ} (R : Type*) [CommRing R] (i : Fin m) (b : Bool) :
    MvPolynomial (Fin m) R :=
  if b then X i else 1 - X i

open MvPolynomial Finset in
/-- The monomial associated to a Boolean assignment `a : Fin m → Bool`:
`∏ᵢ edgeFactor R i (a i)`, i.e. the product `∏ᵢ Xᵢ^{aᵢ} (1 - Xᵢ)^{1 - aᵢ}`.
Over a Boolean point `x`, this is the indicator `[x = a]`. -/
noncomputable def pathMonomial {m : ℕ} (R : Type*) [CommRing R] (a : Fin m → Bool) :
    MvPolynomial (Fin m) R :=
  ∏ i : Fin m, edgeFactor R i (a i)

open MvPolynomial Finset in
/-- Arithmetization of a Boolean function `f : 2^m → 2` as a multilinear
polynomial: sum of `pathMonomial R a` over all assignments `a` with `f a =
true`. On Boolean inputs this evaluates to `1` iff `f a = true`. -/
noncomputable def arithmetizeFn {m : ℕ} (R : Type*) [CommRing R]
    (f : (Fin m → Bool) → Bool) : MvPolynomial (Fin m) R :=
  ∑ a ∈ Finset.univ.filter (fun a => f a = true), pathMonomial R a

open MvPolynomial Finset in
/-- Arithmetization of a branching program `bp`: the multivariate polynomial
representing the Boolean function `bp.eval`. Two equivalent ROBPs arithmetize
to equal polynomials, which is the algebraic core of the `EQ_ROBP ∈ BPP`
proof. -/
noncomputable def arithmetize {m : ℕ} (R : Type*) [CommRing R]
    (bp : BranchingProgram m) : MvPolynomial (Fin m) R :=
  arithmetizeFn R bp.eval

end Probabilistic
