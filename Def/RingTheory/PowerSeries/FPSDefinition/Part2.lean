/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.RingTheory.PowerSeries.InfiniteProducts2.Part6
import Lemma.PowerSeries.InfiniteProducts2
import Theorem.RingTheory.PowerSeries.FPSDefinition
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

end FPS
end AlgebraicCombinatorics
