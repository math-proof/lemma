/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Ideal/Counting.lean -/

/-
Author: @toskua, Avocado
-/

import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
open scoped NumberField


namespace NumberField

namespace Ideal

variable (K : Type*) [Field K] [NumberField K]

/-!
# Counting ideals of bounded norm

This file proves an explicit upper bound on the number of nonzero ideals of the
ring of integers of a number field with absolute norm at most `M`.

## Source and statement map

The exact source is ATLAS corpus record `NumberTheoryI:295`, *Number Theory I*,
Section 14.5, Lemma 14.21. At ATLAS revision
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`, its
[corpus entry](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/targets.yaml#L2072-L2077)
and the corresponding
[Lean wrapper](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/Chapter14/ClassGroupFinite.lean#L29-L32)
are immutable references. The wrapper declaration is
`ClassGroupFinite.ideals_bounded_absNorm_card_le`.

The source statement is: “Let `K` be a number field of degree `n` and let
`M ∈ ℝ_{>0}`. The number of `𝓞_K`-ideals of norm `N(I) ≤ M` is bounded by
`(nM)^(log₂ M)` (and in particular, finite).”

The exact clause-by-clause formalization is
`card_nonzero_absNorm_le_real_rpow`:

* “number field `K` of degree `n`” is `[Field K] [NumberField K]` with
  `n = Module.finrank ℚ K`;
* “`M ∈ ℝ_{>0}`” is `M : ℝ` together with `hM : 0 < M`, with no additional
  endpoint restriction;
* “ideals with `N(I) ≤ M`” is the subtype of `I : Ideal (𝓞 K)` satisfying
  `I ≠ ⊥` and `(Ideal.absNorm I : ℝ) ≤ M`;
* “the number” is `Nat.card` of that subtype, cast to `ℝ`;
* the source bound is represented literally as
  `((Module.finrank ℚ K : ℝ) * M) ^ Real.logb 2 M`, where the real exponent
  notation is Mathlib's `Real.rpow`.

The integer theorem `card_nonzero_absNorm_le` and floor theorem
`card_nonzero_absNorm_le_real` are derived discrete strengthenings used to
prove the source endpoint; they are not claimed as literal source statements.

## Main results

* `NumberField.Ideal.card_nonzero_absNorm_le`: the number of nonzero ideals `I`
  of `𝓞 K` with `Ideal.absNorm I ≤ M` is at most
  `(Module.finrank ℚ K * M) ^ Nat.log 2 M`, for every `M : ℕ`.
* `NumberField.Ideal.card_nonzero_absNorm_le_real`: the same bound with a real
  threshold `M`, stated in terms of `⌊M⌋₊` (the stronger discrete bridge).
* `NumberField.Ideal.card_nonzero_absNorm_le_real_rpow`: the textbook's exact
  positive-real endpoint, with bound `((finrank : ℝ) * M) ^ Real.logb 2 M`
  via real `rpow`, derived from the floor bridge.

## Proof sketch

Every nonzero ideal factors uniquely into prime ideals, each of norm at least
`2`, so an ideal of norm at most `M` has at most `Nat.log 2 M` prime factors
counted with multiplicity. A prime ideal above a rational prime `p` satisfies
`absNorm P = p ^ inertiaDeg`, so every prime factor lies above a rational
prime `p ≤ M`; at most `finrank ℚ K` primes lie above each `p` since
ramification indices and inertia degrees are positive and sum to the degree
(`Ideal.sum_ramification_inertia_eq_finrank`). Padding the factor list with
`none` injects the bounded ideals into `Fin (Nat.log 2 M) → Option fibers`,
which gives the power bound.

## Derivation of the source endpoint

The textbook states this lemma with a positive real threshold `M` and bound
`(n * M) ^ log₂ M`. The integer-threshold theorem above is the strongest
discrete form: it is computable and holds for all `M : ℕ` including `0` and
`1` (where both sides degenerate correctly). The real-`⌊M⌋₊` corollary is the
bridge: for `M < 1` the subtype is empty, and for `1 ≤ M` the real and integer
subtypes coincide. The real-`rpow` theorem is the exact source endpoint,
stating the textbook bound literally with real `rpow`; it follows from the
floor bridge by monotonicity of `rpow` in both base and exponent.
-/

/-- The subtype of nonzero ideals of bounded absolute norm is finite. -/
noncomputable instance instFiniteIdealsBoundedAbsNorm (M : ℕ) :
    Finite {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ M} :=
  ((Ideal.finite_setOfPred_absNorm_le M).subset fun _ hI => hI.2).to_subtype

end Ideal
end NumberField
