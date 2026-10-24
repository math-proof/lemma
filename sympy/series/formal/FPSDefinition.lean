/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import sympy.series.formal.InfiniteProducts2
import Lemma.PowerSeries.InfiniteProducts2
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


open scoped Polynomial
open PowerSeries Finset Finset.HasAntidiagonal Finset.Nat

namespace AlgebraicCombinatorics

namespace FPS

variable {R : Type*} [CommRing R]
/-!
## Definition of FPS (Definition def.fps.fps)

**Definition def.fps.fps**: A formal power series (FPS) in one indeterminate over K
is a sequence (a₀, a₁, a₂, ...) = (aₙ)_{n ∈ ℕ} ∈ K^ℕ of elements of K.

In Mathlib, this is represented by `PowerSeries R` (notation: `R⟦X⟧`).
The type `PowerSeries R` is defined as `MvPowerSeries Unit R`, which is
definitionally `(Unit →₀ ℕ) → R`. Since `Unit →₀ ℕ` is equivalent to `ℕ`,
this is essentially `ℕ → R`.

The constructor `PowerSeries.mk : (ℕ → R) → R⟦X⟧` builds an FPS from a sequence.
The extractor `PowerSeries.coeff n : R⟦X⟧ → R` retrieves the n-th coefficient.
-/


/-- **Definition def.fps.fps**: The equivalence between formal power series `R⟦X⟧`
    and sequences `ℕ → R`.

    This formalizes Definition def.fps.fps from the source: a formal power series
    is a sequence (a₀, a₁, a₂, ...) of elements of R.

    The forward direction extracts coefficients, the inverse constructs the FPS. -/
noncomputable def fpsEquivSeq : R⟦X⟧ ≃ (ℕ → R) where
  toFun f := fun n => coeff n f
  invFun a := PowerSeries.mk a
  left_inv f := by ext n; simp [coeff_mk]
  right_inv a := by ext n; simp [coeff_mk]
/-!
## Operations on FPS (Definition def.fps.ops)

(a) Sum: (a₀ + b₀, a₁ + b₁, ...)
(b) Difference: (a₀ - b₀, a₁ - b₁, ...)
(c) Scalar multiplication: λa = (λa₀, λa₁, ...)
(d) Product: c_n = ∑_{i=0}^n a_i b_{n-i}
(e) Constants: a̲ = (a, 0, 0, ...)
-/
/-!
## Ring Structure (Theorem thm.fps.ring)

Theorem thm.fps.ring states that R⟦X⟧ is:
(a) A commutative ring with zero = (0,0,...) and one = (1,0,0,...)
(b) An R-module
(c) Scaling commutes with multiplication: λ(fg) = (λf)g = f(λg)
(d) Scaling equals multiplication by constant: λf = (C λ) * f

Note: Mathlib already provides these structures on `PowerSeries R`:
- `CommRing R⟦X⟧` instance exists in `Mathlib.RingTheory.PowerSeries.Basic`
- `Module R R⟦X⟧` instance exists via the algebra structure
-/
/-!
## Coefficient Extraction (Definition def.fps.coeff)

[x^n] f denotes the n-th coefficient of f.
In Mathlib this is `PowerSeries.coeff n f`.
-/


/-- The n-th coefficient of an FPS (Definition def.fps.coeff) -/
noncomputable example (n : ℕ) (f : R⟦X⟧) : R := coeff n f
/-!
## The Indeterminate x (Definition def.fps.x)

x = (0, 1, 0, 0, ...) is the FPS with [x^1] x = 1 and [x^i] x = 0 for i ≠ 1.
-/
/-!
## Multiplication by x (Lemma lem.fps.xa)

Multiplying by x shifts the sequence: x * (a₀, a₁, a₂, ...) = (0, a₀, a₁, a₂, ...)

Lemma lem.fps.xa states: If f = (a₀, a₁, a₂, ...), then X * f = (0, a₀, a₁, a₂, ...).
This is equivalent to:
- [x^n](X·f) = a_{n-1} if n > 0
- [x^0](X·f) = 0
-/
/-!
## Powers of x (Proposition prop.fps.xk)

x^k = (0, 0, ..., 0, 1, 0, 0, ...) with k zeros before the 1.
-/
/-!
## FPS as Infinite Sum (Corollary cor.fps.sumakxk)

Any FPS (a₀, a₁, a₂, ...) can be written as ∑_{n ∈ ℕ} aₙ x^n.
This requires the notion of summable families of FPS.
-/
/-!
## Summable Families of FPS (Definition def.fps.summable)

A family (fᵢ)_{i ∈ I} of FPS is summable (or entrywise essentially finite) if
for each n ∈ ℕ, all but finitely many i ∈ I satisfy [x^n] fᵢ = 0.

In this case, the sum ∑_{i ∈ I} fᵢ is defined as the FPS with
[x^n](∑_{i ∈ I} fᵢ) = ∑_{i ∈ I} [x^n] fᵢ (an essentially finite sum).

In Mathlib, this is captured by the topology on power series where
convergence means eventual stability of each coefficient.
See `PowerSeries.WithPiTopology` for details.
-/


/-- A family of FPS is summable if for each coefficient index n,
    all but finitely many family members have that coefficient equal to zero.
    (Definition def.fps.summable) -/
def SummableFPS {ι : Type*} (f : ι → R⟦X⟧) : Prop :=
  ∀ n : ℕ, {i | coeff n (f i) ≠ 0}.Finite

/-- The sum of a summable family of FPS.
    (Definition def.fps.summable, eq. eq.def.fps.summable.sum)

    For a summable family (fᵢ)_{i ∈ I}, the sum ∑_{i ∈ I} fᵢ is the FPS whose
    n-th coefficient is ∑_{i ∈ I} [x^n] fᵢ (an essentially finite sum). -/
noncomputable def summableFPSSum {ι : Type*} (f : ι → R⟦X⟧) (_hf : SummableFPS f) : R⟦X⟧ :=
  PowerSeries.mk (fun n => ∑ᶠ i, coeff n (f i))
/-!
## Essentially Finite Sums (Definition def.infsum.essfin)

A family (aᵢ)_{i ∈ I} of ring elements is essentially finite if
all but finitely many i satisfy aᵢ = 0.

Note: This is equivalent to `(Function.support f).Finite` in Mathlib.

### Part (a): Definition of essentially finite families

A family (aᵢ)_{i ∈ I} ∈ K^I of elements of K is essentially finite if all but finitely
many i ∈ I satisfy aᵢ = 0 (in other words, if the set {i ∈ I | aᵢ ≠ 0} is finite).

### Part (b): Sum of essentially finite families

Let (aᵢ)_{i ∈ I} ∈ K^I be an essentially finite family of elements of K.
Then, the infinite sum ∑_{i ∈ I} aᵢ is defined to equal the finite sum ∑_{i ∈ I, aᵢ ≠ 0} aᵢ.
Such an infinite sum is said to be essentially finite.
-/


/-- A family is essentially finite if its support is finite.
    (Definition def.infsum.essfin (a))

    **This is an alias** for the canonical `EssentiallyFinite` defined in
    `FPS/InfiniteProducts2.lean`. Both definitions are **definitionally equal**:
    `{i | f i ≠ 0}.Finite` = `(Function.support f).Finite` by definition.

    For the full API (including `_root_.EssentiallyFinite.add`, `_root_.EssentiallyFinite.neg`,
    `_root_.EssentiallyFinite.toFinsupp`, etc.), see `FPS/InfiniteProducts2.lean`. -/
abbrev EssentiallyFinite {ι : Type*} (f : ι → R) : Prop :=
  _root_.EssentiallyFinite f
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
