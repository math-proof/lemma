/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/FiniteCongruence.lean -/

import Theorem.NumberTheory.NumberField.RayClass.RayGroup.Part3
import Lemma.Nat.NumberField.RayClass.RayGroup
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.FractionalIdeal.Operations
import Def.NumberTheory.NumberField.RayClass.FiniteCongruence.Part3
@[expose] noncomputable section

open scoped nonZeroDivisors

/-!
# Finite congruence, the finite ray-one subgroup, and admissible representatives (N406)

Source mapping (documentation only; no statement/proof changes):
* ATLAS source: [`v1/Atlas/NumberTheoryI/code/RayClassFields.lean`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L1206-L2011),
  NumberTheoryI N406, Theorem 21.8, Section 21.3; the final declaration is
  [`RayClassField.theorem_21_8_quotient_iso`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L2607-L2647).
* Full source target: the ray-class exact sequence and canonical isomorphism
  `K^m / K^{m,1} ≃ {±1}^{#m∞} × (O_K / m₀)ˣ`. This file is only a finite-kernel
  prerequisite toward that target, not the full theorem.

Helper for ray-class congruence arguments: if `x + y ≠ 0` and both principal
fractional ideals `(x)`, `(y)` have `v`-adic count at least `n`, then so does
`(x + y)`. The nonzero cases go through the `v`-adic valuation and its
nonarchimedean inequality; the zero-summand cases are handled separately.

Main results:
* `rayElement_count_spanSingleton_eq_zero`: a member of `rayElements m` has
  principal fractional-ideal count zero at every finite prime supported by `m`.
* `rayElement_valuation_eq_one`: a ray element has valuation one at every finite
  prime supported by `m`.
* `mem_rayElements_of_valuation_eq_one`: converse valuation-one criterion —
  valuation one at every finite prime supported by `m` gives a ray element.
* `CongruentOneAtFinitePart.mul` / `.inv`: closure of the finite-part
  congruence under multiplication and inversion for ray elements.
* `finiteRayOneElements`: the subgroup of `rayElements m` cut out by the
  finite-part congruence.
* `exists_isUnit_mod_finitePart_div_eq`: every ray element is a quotient of
  two integers both coprime to the finite part of the modulus.
* `quotientUnits_div_eq_of_div_eq`: equal fraction values give equal
  finite-quotient units.
* `finiteResidueMap`: the finite-part residue homomorphism on ray elements.
* `finiteResidueMap_apply_of_div_eq`: computation API for `finiteResidueMap`
  from any admissible representative pair.
* `finiteResidueMap_eq_one_iff`: kernel of `finiteResidueMap` is the
  finite-part congruence.
* `finiteResidueMap_ker`: the kernel of `finiteResidueMap` equals
  `finiteRayOneElements`.
* `finiteResidueMap_eq_one_of_valuation_le`: valuation criterion for triviality
  of `finiteResidueMap` at every supported finite place.

Cumulative finite-kernel source map toward `RayClassField.theorem_21_8_quotient_iso`:
* PR #1035, `count_spanSingleton_add_ge_of_ne_zero`: principal-ideal-count
  counterpart of the finite-congruence multiplication step in
  `RayClassField.UnitsCongruent_subgroup'`; the source rewrites
  `ab - 1 = a * (b - 1) + (a - 1)` and applies `Valuation.map_add`, while the
  helper isolates preservation of a shared count bound under addition.
* PR #1039, `CongruentOneAtFinitePart.mul`, `.inv`, `finiteRayOneElements`:
  `rayElements m` corresponds to ambient `UnitsCoprime_subgroup' K 𝔪`, while
  `finiteRayOneElements m` packages exactly the finite congruence component of
  `UnitsCongruent_subgroup' K 𝔪`; the `mul`/`inv` proofs correspond to its
  finite-place `mul_mem'`/`inv_mem'` clauses, its separate infinite-place
  positivity clause lying outside this finite subgroup.
* PR #1043, `rayElement_valuation_eq_one`, `exists_isUnit_mod_finitePart_div_eq`:
  the former realizes the supported-place normalized-valuation-one property in
  ambient `UnitsCoprime_subgroup' K 𝔪` (compare
  `valuation_eq_one_of_spanSingleton_coprime'`); the latter is the native-API
  counterpart of `coprime_rep_exists`, writing a ray element as `a / b` with
  both integral images units modulo the finite part.
* PR #1046, `finiteResidueMap`, `finiteResidueMap_apply_of_div_eq`: native-API
  counterpart of `finitePartMapHom`; the computation theorem and its private
  implementation encode `coprime_rep_well_def`, namely independence of the
  admissible `a / b` and the value `a * b⁻¹` in quotient units.
* PR #1052, `finiteResidueMap_eq_one_iff`, `finiteResidueMap_ker`: native-API
  counterpart of `finitePartMapHom_ker_iff` and its subgroup-kernel packaging,
  identifying the kernel with `finiteRayOneElements` for the kernel computation
  used by `RayClassField.theorem_21_8_quotient_iso`.
* PR #1093, `mem_rayElements_of_valuation_eq_one`: converse bridge from
  normalized valuation one at every supported finite place to `rayElements m`
  membership; corresponds to the membership condition built into
  `UnitsCoprime_subgroup' K 𝔪`, used in `weak_approx_coprime_sign_finitePart`
  when its controlled approximation witness is packaged as an ambient coprime
  unit.
* PR #1107, `finiteResidueMap_eq_one_of_valuation_le`: the direct
  valuation-bound criterion for trivial finite residue, packaging the
  finite-place congruence implication used in the kernel calculation.
-/


namespace NumberField

namespace Modulus

variable {K : Type*} [Field K] [NumberField K]

/-- Computation API for `finiteResidueMap` from any admissible pair.
Source (N406 §21.3): the representation-independence computation
[`coprime_rep_well_def`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L1757-L1810)
for the finite component. -/
theorem finiteResidueMap_apply_of_div_eq
    (m : Modulus K) (x : rayElements m) (a b : 𝓞 K)
    (ha : IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) a))
    (hb : IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) b))
    (hab : algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b =
      ((x : Kˣ) : K)) :
    finiteResidueMap m x = ha.unit * hb.unit⁻¹ :=
  finiteResidueMapFn_eq_of_div_eq m x a b ha hb hab

theorem not_mem_of_isUnit_quotient_mk
    {R : Type*} [CommRing R] {I p : Ideal R} (hIp : I ≤ p)
    (hp : p ≠ ⊤) {b : R}
    (hb : IsUnit (Ideal.Quotient.mk I b)) : b ∉ p := by
  have H : ∀ a : R, a ∈ I → Ideal.Quotient.mk p a = 0 :=
    fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (hIp ha)
  have hunit : IsUnit (Ideal.Quotient.lift I (Ideal.Quotient.mk p) H
      (Ideal.Quotient.mk I b)) := hb.map _
  rw [Ideal.Quotient.lift_mk] at hunit
  intro hmem
  have hzero : Ideal.Quotient.mk p b = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  rw [hzero] at hunit
  let _ : Nontrivial (R ⧸ p) := Ideal.Quotient.nontrivial_iff.mpr hp
  exact not_isUnit_zero hunit

theorem finiteExponent_eq_count_normalizedFactors
    (m : Modulus K)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    finiteExponent m v =
      ((UniqueFactorizationMonoid.normalizedFactors
          (m.finitePart : Ideal (𝓞 K))).count v.asIdeal : ℤ) := by
  have hne : (m.finitePart : Ideal (𝓞 K)) ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp m.finitePart.property
  unfold finiteExponent
  rw [FractionalIdeal.count_coe,
    Ideal.count_associates_factors_eq hne v.isPrime v.ne_bot]
  exact hne

theorem mem_finitePart_iff_forall_primePow_mem
    (m : Modulus K) (r : 𝓞 K) :
    r ∈ (m.finitePart : Ideal (𝓞 K)) ↔
      ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        finiteSupported m v →
          r ∈ v.asIdeal ^
            (UniqueFactorizationMonoid.normalizedFactors
              (m.finitePart : Ideal (𝓞 K))).count v.asIdeal := by
  have hI : (m.finitePart : Ideal (𝓞 K)) ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp m.finitePart.property
  conv_lhs => rw [← Ideal.iInf_maxPowDividing_eq hI]
  rw [Ideal.mem_iInf]
  constructor
  · intro h v hv
    have hv' := h v
    rwa [IsDedekindDomain.HeightOneSpectrum.maxPowDividing_eq_pow_multiset_count
      v hI] at hv'
  · intro h v
    rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing_eq_pow_multiset_count
      v hI]
    by_cases hv : finiteSupported m v
    · exact h v hv
    · have hcount : (UniqueFactorizationMonoid.normalizedFactors
          (m.finitePart : Ideal (𝓞 K))).count v.asIdeal = 0 := by
        apply Multiset.count_eq_zero.mpr
        intro hmem
        have hdvd : v.asIdeal ∣ (m.finitePart : Ideal (𝓞 K)) :=
          UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hmem
        have hle : (m.finitePart : Ideal (𝓞 K)) ≤ v.asIdeal :=
          Ideal.dvd_iff_le.mp hdvd
        exact hv hle
      simp only [hcount, pow_zero, Ideal.one_eq_top, Submodule.mem_top]

theorem quotientUnits_div_eq_one_iff_sub_mem
    (m : Modulus K) (a b : 𝓞 K)
    (ha : IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) a))
    (hb : IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) b)) :
    ha.unit * hb.unit⁻¹ = 1 ↔ a - b ∈ (m.finitePart : Ideal (𝓞 K)) := by
  rw [mul_inv_eq_one]
  constructor
  · intro h
    have hval := congrArg Units.val h
    simp only [IsUnit.unit_spec] at hval
    exact Ideal.Quotient.eq.mp hval
  · intro h
    apply Units.ext
    simp only [IsUnit.unit_spec]
    exact Ideal.Quotient.eq.mpr h

theorem valuation_sub_one_eq_intValuation_sub
    (m : Modulus K) (x : rayElements m) (a b : 𝓞 K)
    (hb : IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) b))
    (hab : algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b =
      ((x : Kˣ) : K))
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hv : finiteSupported m v) :
    v.valuation K (((x : Kˣ) : K) - 1) = v.intValuation (a - b) := by
  have hbNotMem : b ∉ v.asIdeal :=
    not_mem_of_isUnit_quotient_mk hv v.isPrime.ne_top hb
  have hintB : v.intValuation b = 1 :=
    IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr hbNotMem
  have hbK : algebraMap (𝓞 K) K b ≠ 0 := by
    intro h0
    have hb0 : b = 0 :=
      IsFractionRing.injective (𝓞 K) K (by rw [h0, map_zero])
    exact hbNotMem (by rw [hb0]; exact Submodule.zero_mem _)
  have hfrac : ((x : Kˣ) : K) - 1 =
      algebraMap (𝓞 K) K (a - b) / algebraMap (𝓞 K) K b := by
    rw [← hab, map_sub]
    field_simp
  rw [hfrac, Valuation.map_div,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, hintB,
    div_one]

theorem quotientUnits_div_eq_one_iff_congruent
    (m : Modulus K) (x : rayElements m) (a b : 𝓞 K)
    (ha : IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) a))
    (hb : IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) b))
    (hab : algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b =
      ((x : Kˣ) : K)) :
    ha.unit * hb.unit⁻¹ = 1 ↔ CongruentOneAtFinitePart m (x : Kˣ) := by
  rw [quotientUnits_div_eq_one_iff_sub_mem m a b ha hb,
    mem_finitePart_iff_forall_primePow_mem m (a - b)]
  constructor
  · intro h v hv
    by_cases hx : ((x : Kˣ) : K) = 1
    · exact Or.inl hx
    · refine Or.inr ?_
      have hmem := h v hv
      set n := (UniqueFactorizationMonoid.normalizedFactors
        (m.finitePart : Ideal (𝓞 K))).count v.asIdeal with hn
      have hle : v.intValuation (a - b) ≤ WithZero.exp (-(n : ℤ)) :=
        (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem
          v (a - b) n).mpr hmem
      have hval := valuation_sub_one_eq_intValuation_sub m x a b hb hab v hv
      have hne : ((x : Kˣ) : K) - 1 ≠ 0 := sub_ne_zero.mpr hx
      have hexp := valuation_eq_exp_neg_count v hne
      rw [← hval] at hle
      rw [hexp, WithZero.exp_le_exp] at hle
      have hfe := finiteExponent_eq_count_normalizedFactors m v
      rw [← hn] at hfe
      omega
  · intro h v hv
    set n := (UniqueFactorizationMonoid.normalizedFactors
      (m.finitePart : Ideal (𝓞 K))).count v.asIdeal with hn
    by_cases hx : ((x : Kˣ) : K) = 1
    · have hbNotMem : b ∉ v.asIdeal :=
        not_mem_of_isUnit_quotient_mk hv v.isPrime.ne_top hb
      have hbK : algebraMap (𝓞 K) K b ≠ 0 := by
        intro h0
        have hb0 : b = 0 :=
          IsFractionRing.injective (𝓞 K) K (by rw [h0, map_zero])
        exact hbNotMem (by rw [hb0]; exact Submodule.zero_mem _)
      have h1 : algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b = 1 := by
        rw [hab, hx]
      have hab1 : algebraMap (𝓞 K) K a = algebraMap (𝓞 K) K b :=
        (div_eq_one_iff_eq hbK).mp h1
      have hab0 : a - b = 0 := by
        apply IsFractionRing.injective (𝓞 K) K
        rw [map_sub, hab1, sub_self, map_zero]
      rw [hab0]
      exact Submodule.zero_mem _
    · have hle := (h v hv).resolve_left hx
      have hne : ((x : Kˣ) : K) - 1 ≠ 0 := sub_ne_zero.mpr hx
      have hexp := valuation_eq_exp_neg_count v hne
      have hval := valuation_sub_one_eq_intValuation_sub m x a b hb hab v hv
      have hfe := finiteExponent_eq_count_normalizedFactors m v
      rw [← hn] at hfe
      have hcount : -(FractionalIdeal.count K v
          (FractionalIdeal.spanSingleton (𝓞 K)⁰
            (((x : Kˣ) : K) - 1))) ≤ -((n : ℕ) : ℤ) := by
        omega
      have hle' : v.valuation K (((x : Kˣ) : K) - 1) ≤
          WithZero.exp (-((n : ℕ) : ℤ)) := by
        rw [hexp, WithZero.exp_le_exp]
        exact hcount
      rw [hval] at hle'
      exact (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem
        v (a - b) n).mp hle'

/-- The finite residue map is trivial exactly on the finite-part congruence.
Source (N406 §21.3): helper
[`finitePartMapHom_ker_iff`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L1996-L2011). -/
theorem finiteResidueMap_eq_one_iff (m : Modulus K) (x : rayElements m) :
    finiteResidueMap m x = 1 ↔ CongruentOneAtFinitePart m (x : Kˣ) := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_isUnit_mod_finitePart_div_eq m x
  rw [finiteResidueMap_apply_of_div_eq m x a b ha hb hab]
  exact quotientUnits_div_eq_one_iff_congruent m x a b ha hb hab

/-- The kernel of the finite residue map is `finiteRayOneElements`.
Source (N406 §21.3): the finite kernel component used in the
[`theorem_21_8_quotient_iso`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L2600-L2647). -/
theorem finiteResidueMap_ker (m : Modulus K) :
    (finiteResidueMap m).ker = finiteRayOneElements m := by
  ext x
  simp only [MonoidHom.mem_ker, mem_finiteRayOneElements_iff,
    finiteResidueMap_eq_one_iff]

/-- Valuation criterion for triviality of the finite residue map: a valuation bound
on `z - 1` at every supported finite place forces `finiteResidueMap m z = 1`.

Source mapping (N406, Theorem 21.8, Section 21.3; ATLAS NumberTheoryI item N406):
the native-API finite-congruence step corresponding to
[`finitePartMapHom_ker_iff`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L1996-L2011),
used by the weak-approximation argument before residue/sign surjectivity and by
[`theorem_21_8_quotient_iso`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L2607-L2647).
It is not the generalized weak-approximation theorem and not the final N406
result. -/
theorem finiteResidueMap_eq_one_of_valuation_le
    (m : Modulus K) (z : rayElements m)
    (h : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      finiteSupported m v →
        v.valuation K (((z : Kˣ) : K) - 1) ≤
          WithZero.exp (-(finiteExponent m v))) :
    finiteResidueMap m z = 1 := by
  rw [finiteResidueMap_eq_one_iff]
  intro v hv
  by_cases hx : (((z : Kˣ) : K)) = 1
  · exact Or.inl hx
  · refine Or.inr ?_
    have hne : (((z : Kˣ) : K) - 1) ≠ 0 := sub_ne_zero.mpr hx
    have hexp := valuation_eq_exp_neg_count v hne
    have hle := h v hv
    rw [hexp, WithZero.exp_le_exp] at hle
    omega

end Modulus
end NumberField
