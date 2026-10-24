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

/-- Prime ideals of `𝓞 K` lying above rational primes `p ≤ M`, bundled by `p`. -/
private abbrev primeFibers (M : ℕ) :=
  (p : {p : ℕ // p.Prime ∧ p ≤ M}) ×
    ↥((Ideal.span ({(p.1 : ℤ)} : Set ℤ)).primesOver (𝓞 K))

/-- Per-fiber `Fintype`: a nonzero prime of `ℤ` is maximal, so each
`primesOver` set is finite. -/
private noncomputable instance fiberFintype (M : ℕ)
    (p : {p : ℕ // p.Prime ∧ p ≤ M}) :
    Fintype ↥((Ideal.span ({(p.1 : ℤ)} : Set ℤ)).primesOver (𝓞 K)) := by
  have hcast : ((p.1 : ℕ) : ℤ) ≠ 0 := by exact_mod_cast p.2.1.ne_zero
  have hprime : (Ideal.span ({(p.1 : ℤ)} : Set ℤ)).IsPrime :=
    (Ideal.span_singleton_prime hcast).mpr (Nat.prime_iff_prime_int.mp p.2.1)
  have hP0 : Ideal.span ({(p.1 : ℤ)} : Set ℤ) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hcast
  have hmax : (Ideal.span ({(p.1 : ℤ)} : Set ℤ)).IsMaximal :=
    hprime.isMaximal hP0
  infer_instance

/-- `Fintype` for the rational primes bounded by `M`. -/
private noncomputable instance instFintypePrimeBounds (M : ℕ) :
    Fintype {p : ℕ // p.Prime ∧ p ≤ M} := by
  have hfin : {p : ℕ | p.Prime ∧ p ≤ M}.Finite :=
    (Finset.range (M + 1)).finite_toSet.subset fun p hp =>
      Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.lt_succ_of_le hp.2))
  exact hfin.fintype

private noncomputable instance instFintypePrimeFibers (M : ℕ) :
    Fintype (primeFibers K M) := by
  infer_instance

/-- Every bounded nonzero prime ideal lies above a small rational prime. -/
private theorem exists_prime_liesOver {P : Ideal (𝓞 K)} (M : ℕ)
    (hprime : P.IsPrime) (hbot : P ≠ ⊥) (hle : Ideal.absNorm P ≤ M) :
    ∃ p : ℕ, p.Prime ∧ p ≤ M ∧
      P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := by
  have hPprime : P.IsPrime := hprime
  haveI := hprime
  obtain ⟨q, hq⟩ := IsPrincipalIdealRing.principal (P.under ℤ)
  have hqspan : Ideal.span ({q} : Set ℤ) = P.under ℤ := hq.symm
  have hq0 : q ≠ 0 := by
    rintro rfl
    apply hbot
    have hunder : P.under ℤ = ⊥ := by
      rw [← hqspan]
      exact Ideal.span_singleton_eq_bot.mpr rfl
    exact Ideal.eq_bot_of_under_eq_bot hunder
  have hgen_prime : (Ideal.span ({q} : Set ℤ)).IsPrime := by
    rw [hqspan]
    infer_instance
  have hqprime : Prime q := (Ideal.span_singleton_prime hq0).mp hgen_prime
  have hspan : Ideal.span ({((q.natAbs : ℕ) : ℤ)} : Set ℤ) =
      Ideal.span ({q} : Set ℤ) := by
    rcases abs_choice q with h | h <;> simp [h]
  have hlie : P.LiesOver (Ideal.span ({q} : Set ℤ)) := by
    rcases abs_choice q with h | h <;>
      simpa [h, Ideal.span_singleton_neg q, ← Ideal.submodule_span_eq, ← hq]
        using Ideal.over_under P
  have hlieN : P.LiesOver (Ideal.span ({((q.natAbs : ℕ) : ℤ)} : Set ℤ)) := by
    rw [hspan]
    exact hlie
  have hlieI : P.LiesOver (Ideal.span ({((q.natAbs : ℕ) : ℤ)} : Set ℤ)) := hlieN
  haveI := hlieN
  have hpow := Ideal.pow_inertiaDeg q.natAbs P
  have hpos : 0 < P.inertiaDeg ℤ := Ideal.inertiaDeg_pos P ℤ
  have h1 : 1 ≤ q.natAbs := Int.natAbs_pos.mpr hq0
  refine ⟨q.natAbs, Int.prime_iff_natAbs_prime.mp hqprime, ?_, hlieN⟩
  calc q.natAbs ≤ q.natAbs ^ P.inertiaDeg ℤ := le_self_pow₀ h1 hpos.ne'
    _ = Ideal.absNorm P := hpow
    _ ≤ M := hle

/-- Prime factors of a bounded ideal are prime, nonzero, and bounded. -/
private theorem factor_props {M : ℕ} {I : Ideal (𝓞 K)}
    (hI : I ≠ ⊥) (hle : Ideal.absNorm I ≤ M)
    {P : Ideal (𝓞 K)}
    (hP : P ∈ UniqueFactorizationMonoid.normalizedFactors I) :
    P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P ≤ M := by
  obtain ⟨hprime, hleIP⟩ := (Ideal.mem_normalizedFactors_iff hI).mp hP
  have hPbot : P ≠ ⊥ := by
    rintro rfl
    exact hI (le_bot_iff.mp hleIP)
  have hdvd : P ∣ I :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP
  have hnorm : Ideal.absNorm P ∣ Ideal.absNorm I :=
    Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hdvd)
  have hne : Ideal.absNorm I ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hI
  have hPle : Ideal.absNorm P ≤ M :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hnorm).trans hle
  exact ⟨hprime, hPbot, hPle⟩

/-- The fiber element over a prime factor; a pure term so projections hold
by `rfl`. -/
private noncomputable def fiberMkAux {M : ℕ} (p : ℕ) (hprimep : p.Prime)
    (hpleM : p ≤ M) {P : Ideal (𝓞 K)} (hprime : P.IsPrime)
    (hlies : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))) :
    primeFibers K M :=
  ⟨⟨p, hprimep, hpleM⟩, P, hprime, hlies⟩

/-- Injection data: the padded factor list of a bounded ideal. -/
private noncomputable def encode (M : ℕ)
    (x : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ M}) :
    Fin (Nat.log 2 M) → Option (primeFibers K M) := fun i =>
  if h : i.val < (UniqueFactorizationMonoid.normalizedFactors x.1).toList.length
  then
    have hPmem : (UniqueFactorizationMonoid.normalizedFactors x.1).toList[i.val]'h ∈
        UniqueFactorizationMonoid.normalizedFactors x.1 :=
      Multiset.mem_toList.mp (List.mem_of_getElem rfl)
    have hprops := factor_props K x.2.1 x.2.2 hPmem
    have hex := exists_prime_liesOver K M hprops.1 hprops.2.1 hprops.2.2
    some (fiberMkAux K hex.choose hex.choose_spec.1 hex.choose_spec.2.1
      hprops.1 hex.choose_spec.2.2)
  else none
end Ideal
end NumberField
