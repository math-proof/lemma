/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.RingTheory.PowerSeries.InfiniteProducts2.Part6
import Lemma.PowerSeries.InfiniteProducts2
import Def.RingTheory.PowerSeries.FPSDefinition
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

end FPS
end AlgebraicCombinatorics
