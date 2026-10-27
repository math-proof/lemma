/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.RingTheory.PowerSeries.InfiniteProducts2.Part6
import Lemma.PowerSeries.InfiniteProducts2
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

end FPS
end AlgebraicCombinatorics
