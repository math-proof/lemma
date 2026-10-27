/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.RingTheory.PowerSeries.InfiniteProducts2.Part6
import Lemma.PowerSeries.InfiniteProducts2
import Abbrev.RingTheory.PowerSeries.FPSDefinition
open scoped Polynomial
open PowerSeries Finset Finset.HasAntidiagonal Finset.Nat

/-!
# Formal Power Series: Definition and Basic Properties

This file formalizes the definition of formal power series (FPS) and their basic operations,
following Section "The definition of formal power series" (subsec.gf.defs.fps) of the source.

## Main definitions

* `fpsEquivSeq` (Definition def.fps.fps): The equivalence between formal power series
  `R⟦X⟧` and sequences `ℕ → R`. This formalizes that an FPS is a sequence (a₀, a₁, a₂, ...).

* We use Mathlib's `PowerSeries R` which represents formal power series over a ring `R`.
  This is defined as `MvPowerSeries Unit R`, i.e., sequences `ℕ → R`.

* `PowerSeries.coeff n f` extracts the n-th coefficient of a power series f.
  This corresponds to `[x^n] f` in the source notation.

* `PowerSeries.mk` constructs a power series from a sequence of coefficients.

* `PowerSeries.X` is the indeterminate x = (0, 1, 0, 0, ...).

* `PowerSeries.C` embeds constants into power series as (a, 0, 0, ...).

## Main results

* `PowerSeries` forms a commutative ring (Theorem thm.fps.ring (a))
* `PowerSeries` is a module over the base ring (Theorem thm.fps.ring (b))
* Scaling by λ equals multiplication by C λ (Theorem thm.fps.ring (d))
* Coefficient extraction is additive and compatible with multiplication
* Multiplication by x shifts coefficients: X * (a₀, a₁, ...) = (0, a₀, a₁, ...) (Lemma lem.fps.xa)
* `x^k` has the form (0, 0, ..., 0, 1, 0, 0, ...) with k zeros (Proposition prop.fps.xk)
* Any FPS can be written as ∑ aₙ xⁿ (Corollary cor.fps.sumakxk)

## References

* Source: FPSDefinition.tex, subsec.gf.defs.fps

## Implementation notes

Mathlib already provides `PowerSeries R` with all the ring structure and basic operations.
This file provides additional lemmas and connects Mathlib's API to the textbook presentation.

For summable families of FPS, we use Mathlib's topological structure on power series
(`PowerSeries.WithPiTopology`), where a family is summable when for each coefficient index,
all but finitely many terms have that coefficient equal to zero.
-/


namespace AlgebraicCombinatorics

namespace FPS

variable {R : Type*} [CommRing R]

/-!
### Sum of an essentially finite family (Definition def.infsum.essfin (b))

For an essentially finite family (aᵢ)_{i ∈ I}, the infinite sum ∑_{i ∈ I} aᵢ
is defined to equal the finite sum ∑_{i ∈ I, aᵢ ≠ 0} aᵢ.

We connect this to Mathlib's `Finsupp.sum` infrastructure.
-/


/-- Finset support of an essentially finite family (unfolds the Prop alias). -/
noncomputable def essFinSupport {ι : Type*} {f : ι → R} (hf : EssentiallyFinite f) : Finset ι :=
  (_root_.EssentiallyFinite.finite_support hf).toFinset

/-- The sum of an essentially finite family, defined as the finite sum over non-zero elements.
    (Definition def.infsum.essfin (b)) -/
noncomputable def essFinSum {ι : Type*} (f : ι → R) (hf : EssentiallyFinite f) : R :=
  ∑ i ∈ essFinSupport hf, f i

/-- Connection to Finsupp: an essentially finite family can be converted to a Finsupp -/
noncomputable def essentiallyFiniteToFinsupp {ι : Type*} (f : ι → R) (hf : EssentiallyFinite f) :
    ι →₀ R :=
  Finsupp.ofSupportFinite f hf

/-!
## Rules for Summable Sums (Proposition prop.fps.summable-sums-rule)

Sums of summable families of FPS satisfy the usual rules for sums:
- Breaking-apart rule: if S = X ∪ Y (disjoint), then ∑_{i ∈ S} fᵢ = ∑_{i ∈ X} fᵢ + ∑_{i ∈ Y} fᵢ
- Fubini rule: ∑_{i ∈ I} ∑_{j ∈ J} fᵢⱼ = ∑_{(i,j) ∈ I×J} fᵢⱼ = ∑_{j ∈ J} ∑_{i ∈ I} fᵢⱼ
  (when the family (fᵢⱼ)_{(i,j) ∈ I×J} is summable)

These properties follow from the corresponding properties of essentially finite sums
applied coefficient-wise.
-/
/-!
## Generating Functions

The (ordinary) generating function of a sequence (a₀, a₁, a₂, ...) is
the FPS (a₀, a₁, a₂, ...) = a₀ + a₁x + a₂x² + ...
-/


/-- The generating function of a sequence is just the FPS with those coefficients -/
def generatingFunction (a : ℕ → R) : R⟦X⟧ := PowerSeries.mk a

/-!
## Vandermonde / Chu-Vandermonde Identity

### For Natural Numbers (Proposition prop.binom.vandermonde.NN)

For a, b, n ∈ ℕ: C(a+b, n) = ∑_{k=0}^n C(a,k) C(b, n-k)
-/
/-!
### For Complex Numbers (Theorem thm.binom.vandermonde.CC)

The Chu-Vandermonde identity extends to all complex numbers (or any binomial ring).
For a, b ∈ ℂ and n ∈ ℕ: C(a+b, n) = ∑_{k=0}^n C(a,k) C(b, n-k)

The proof uses the polynomial identity trick: both sides are polynomials in a and b
that agree on ℕ × ℕ, hence they agree everywhere.
-/

end FPS
end AlgebraicCombinatorics
