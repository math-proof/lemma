/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/MaximalIdealPowQuotientTrace.lean -/

/-
Author: Muse Code
-/

import Mathlib.RingTheory.Trace.Quotient
import Theorem.LinearAlgebra.Trace.InvariantSubmodule
import Lemma.Matrix.Trace.InvariantSubmodule
import Lemma.Int.DiscreteValuationRing.MaximalIdealGradedPieceMul
import Lemma.Int.DiscreteValuationRing.MaximalIdealPowFactor
import Def.RingTheory.DiscreteValuationRing.MaximalIdealGradedPieceMul
import Def.RingTheory.DiscreteValuationRing.MaximalIdealPowFactor.Part3
open IsLocalRing

variable (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
  [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [Algebra A B]
/-!
# One-step trace recurrence for maximal-ideal-power quotients

Let `A` and `B` be commutative-domain discrete valuation rings with an
`A`-algebra structure on `B`. For each `n`, the canonical factor map from the
quotient by `map 𝔪A ⊔ 𝔪B ^ (n + 1)` to the quotient by `map 𝔪A ⊔ 𝔪B ^ n` is a
surjective `ResidueField A`-algebra hom. Under the containment hypothesis
`map 𝔪A ≤ 𝔪B ^ (n + 1)` and the residue-field linear-structure assumptions on
the graded piece (as in the main theorem below), its kernel is identified with
the `n`-th maximal-ideal graded piece of `B`. Left multiplication by a quotient
representative therefore has trace equal to the graded-piece trace plus the
trace on the target quotient.

This module is a prerequisite stage for the corrected ATLAS NumberTheoryI N261
upper different-exponent bound (Theorem 12.27), not the full N261 target. It
proves the one-step trace recurrence, the iterated quotient trace formula
by induction, the integral-trace residue bridge
`residue_intTrace_eq_nsmul_trace_residue_of_map_maximalIdeal_eq_pow`, and the
tame integral-trace surjectivity
`intTrace_surjective_of_isUnit_natCast_of_map_maximalIdeal_eq_pow`: under
`map 𝔪A = 𝔪B ^ e` and `IsUnit (e : B)`, the integral trace is surjective; the
different-ideal containment, either valuation bound, the tame-equality
characterization, and the wild mixed-characteristic fractional trace-dual
estimate remain deferred. The bridge controls the integral trace only modulo
`maximalIdeal A` and does not by itself prove the fractional-dual bound. The
surjectivity result is the tame input only: it is new supporting API, not an
ATLAS source theorem, and not a proof of the wild mixed-characteristic bound.

ATLAS source: [`v1/Atlas/NumberTheoryI/code/DifferentDiscriminant.lean`, lines
1237--1324, at revision `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/DifferentDiscriminant.lean#L1237-L1324).
Those lines define the ramification/different valuations and state the target
bounds, but they do not state the trace recurrence proved here.

Source-to-API map: `trace_residueFieldMaximalIdealPowQuotient_succ`,
`trace_residueFieldMaximalIdealPowQuotient`,
`residue_intTrace_eq_nsmul_trace_residue_of_map_maximalIdeal_eq_pow`, and the
tame integral-trace surjectivity
`intTrace_surjective_of_isUnit_natCast_of_map_maximalIdeal_eq_pow` (under
`map 𝔪A = 𝔪B ^ e` and `IsUnit (e : B)`, the integral trace is surjective) are
new supporting API for the quotient-filtration route to the trace/different
estimate; the different containment, the valuation bounds, the tame-equality
characterization, and the fractional trace-dual estimate remain deferred. The
surjectivity result is the tame input only, not an ATLAS source theorem and not
a proof of the wild mixed-characteristic bound.

## Main results

* `trace_residueFieldMaximalIdealPowQuotient_succ`: the algebra trace of
  multiplication by a representative on quotient index `n + 1` equals the
  residue-field trace of the residue plus the algebra trace on quotient
  index `n`.
* `trace_residueFieldMaximalIdealPowQuotient`: the algebra trace of
  multiplication by a representative on quotient index `n` equals `n` times
  the residue-field trace of the residue.
* `residue_intTrace_eq_nsmul_trace_residue_of_map_maximalIdeal_eq_pow`:
  under `map 𝔪A = 𝔪B ^ e`, the residue of `Algebra.intTrace A B b` equals
  `e` times the residue-field trace of `residue B b`. This is a congruence
  modulo `maximalIdeal A` only; it does not prove the wild
  mixed-characteristic fractional-dual bound.
* `intTrace_surjective_of_isUnit_natCast_of_map_maximalIdeal_eq_pow`: under
  `map 𝔪A = 𝔪B ^ e` and `IsUnit (e : B)`, the integral trace is surjective.
  This is new supporting API for the tame input only; it is not an ATLAS
  source theorem and not a proof of the wild mixed-characteristic bound.
-/


