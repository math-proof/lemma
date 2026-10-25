/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/FiniteCongruence.lean -/

import Theorem.NumberTheory.NumberField.RayClass.RayGroup.Part3
import Lemma.Nat.NumberField.RayClass.RayGroup
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.FractionalIdeal.Operations
import Def.NumberTheory.NumberField.RayClass.FiniteCongruence
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

@[simp] theorem mem_finiteRayOneElements_iff (m : Modulus K)
    (x : rayElements m) :
    x ∈ finiteRayOneElements m ↔ CongruentOneAtFinitePart m (x : Kˣ) :=
  Iff.rfl

/-- Every ray element is a ratio of two integers coprime to the finite part.
Source (N406 §21.3): the
[`coprime_rep_exists`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L1553-L1747)
admissible integral numerator/denominator representation with both residues units. -/
theorem exists_isUnit_mod_finitePart_div_eq
    (m : Modulus K) (x : rayElements m) :
    ∃ a b : 𝓞 K,
      IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) a) ∧
      IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) b) ∧
      algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b = ((x : Kˣ) : K) := by
  classical
  by_cases htriv : Subsingleton (𝓞 K ⧸ (m.finitePart : Ideal (𝓞 K)))
  · obtain ⟨a₀, b₀, _, hab₀⟩ :=
        IsFractionRing.div_surjective (𝓞 K) ((x : Kˣ) : K)
    let _ : Subsingleton (𝓞 K ⧸ (m.finitePart : Ideal (𝓞 K))) := htriv
    exact ⟨a₀, b₀, isUnit_of_subsingleton _, isUnit_of_subsingleton _,
      by rw [← hab₀]⟩
  · rw [not_subsingleton_iff_nontrivial] at htriv
    let _ : Nontrivial (𝓞 K ⧸ (m.finitePart : Ideal (𝓞 K))) := htriv
    obtain ⟨a₀, b₀, hb₀_mem, hab₀⟩ :=
      IsFractionRing.div_surjective (𝓞 K) ((x : Kˣ) : K)
    have hα_ne : ((x : Kˣ) : K) ≠ 0 := Units.ne_zero (x : Kˣ)
    have hα_val : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        finiteSupported m v → v.valuation K ((x : Kˣ) : K) = 1 :=
      fun v hv => rayElement_valuation_eq_one m x v hv
    have hI : (m.finitePart : Ideal (𝓞 K)) ≠ 0 :=
      mem_nonZeroDivisors_iff_ne_zero.mp m.finitePart.property
    set S := (Ideal.finite_factors hI).toFinset with hS_def
    have hS_mem : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        v ∈ S ↔ (m.finitePart : Ideal (𝓞 K)) ≤ v.asIdeal := by
      intro v
      rw [hS_def, Set.Finite.mem_toFinset]
      exact Ideal.dvd_iff_le
    let J : Ideal (𝓞 K) :=
      { carrier := {b | IsLocalization.IsInteger (𝓞 K)
          (algebraMap (𝓞 K) K b * ((x : Kˣ) : K))}
        add_mem' := fun {a b} ha hb => by
          simp only [Set.mem_ofPred_eq, IsLocalization.IsInteger, map_add,
            add_mul] at *
          obtain ⟨ca, hca⟩ := ha
          obtain ⟨cb, hcb⟩ := hb
          exact ⟨ca + cb, by rw [map_add, hca, hcb]⟩
        zero_mem' := by
          simp only [Set.mem_ofPred_eq, map_zero, zero_mul]
          exact ⟨0, map_zero _⟩
        smul_mem' := fun c {b} hb => by
          simp only [Set.mem_ofPred_eq, IsLocalization.IsInteger, smul_eq_mul,
            map_mul, mul_assoc] at *
          obtain ⟨cb, hcb⟩ := hb
          exact ⟨c * cb, by rw [map_mul, hcb]⟩ }
    have hb₀_in_J : b₀ ∈ J := by
      change IsLocalization.IsInteger _ _
      rw [← hab₀, mul_div_cancel₀]
      · exact ⟨a₀, rfl⟩
      · exact map_ne_zero_of_mem_nonZeroDivisors _
          (IsFractionRing.injective (𝓞 K) K) hb₀_mem
    have hJ_ne_bot : J ≠ ⊥ := by
      intro h
      have hmem : b₀ ∈ (⊥ : Ideal (𝓞 K)) := h ▸ hb₀_in_J
      rw [Ideal.mem_bot] at hmem
      exact hα_ne (by rw [← hab₀]; simp [hmem])
    have hJ_not_le : ∀ v ∈ S, ¬(J ≤ v.asIdeal) := by
      intro v hv hle
      have hv_supp : finiteSupported m v := (hS_mem v).mp hv
      have hv_ne_top : v.asIdeal ≠ ⊤ := v.isPrime.ne_top
      obtain ⟨c, hc_int, i, hi_mem, hc_notmem⟩ :=
        Ideal.exist_integer_multiples_notMem (K := K) hv_ne_top
          ({0, 1} : Finset (Fin 2))
          (fun i => if i = 0 then ((x : Kˣ) : K) else 1)
          (j := 1) (by simp) (by simp)
      have hc_is_int : IsLocalization.IsInteger (𝓞 K) c := by
        have h1 := hc_int 1 (by simp)
        simpa using h1
      have hcα_is_int : IsLocalization.IsInteger (𝓞 K)
          (c * ((x : Kˣ) : K)) := by
        have h0 := hc_int 0 (by simp)
        simpa using h0
      obtain ⟨b_int, hb_int⟩ := hc_is_int
      have hb_int_in_J : b_int ∈ J := by
        change IsLocalization.IsInteger _ _
        rw [hb_int]
        exact hcα_is_int
      have hb_int_mem : b_int ∈ v.asIdeal := hle hb_int_in_J
      have hv_c_ne1 : v.valuation K c ≠ 1 := by
        rw [← hb_int,
          IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
        rw [Ne, IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
        exact not_not.mpr hb_int_mem
      have hv_α_eq1 : v.valuation K ((x : Kˣ) : K) = 1 :=
        hα_val v hv_supp
      have hv_cα_ne1 : v.valuation K (c * ((x : Kˣ) : K)) ≠ 1 := by
        rw [map_mul, hv_α_eq1, mul_one]
        exact hv_c_ne1
      obtain ⟨a_int, ha_int⟩ := hcα_is_int
      have ha_int_mem : a_int ∈ v.asIdeal := by
        rw [← not_not (a := a_int ∈ v.asIdeal)]
        rw [← IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
        intro h_eq
        exact hv_cα_ne1 (by
          rw [← ha_int,
            IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
            h_eq])
      rcases i with ⟨i, hi⟩
      interval_cases i
      · simp only [Fin.mk_zero] at hc_notmem
        simp only [ite_true] at hc_notmem
        exact hc_notmem ((FractionalIdeal.mem_coeIdeal _).mpr
          ⟨a_int, ha_int_mem, ha_int⟩)
      · simp only [Fin.mk_one, one_ne_zero, ite_false, mul_one] at hc_notmem
        exact hc_notmem ((FractionalIdeal.mem_coeIdeal _).mpr
          ⟨b_int, hb_int_mem, hb_int⟩)
    have ⟨b, hb_in_J, hb_avoid⟩ : ∃ b ∈ J, ∀ v ∈ S, b ∉ v.asIdeal := by
      by_contra h
      push Not at h
      rcases S.eq_empty_or_nonempty with hS_empty | ⟨v₀, hv₀⟩
      · obtain ⟨v, hv, _⟩ := h b₀ hb₀_in_J
        rw [hS_empty] at hv
        exact (Finset.notMem_empty v hv).elim
      · have hsub : (J : Set (𝓞 K)) ⊆
            ⋃ v ∈ (↑S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))),
              (v.asIdeal : Set _) := by
          intro y hy
          obtain ⟨v, hv, hvx⟩ := h y hy
          exact Set.mem_biUnion (Finset.mem_coe.mpr hv) hvx
        rw [Ideal.subset_union_prime_finite S.finite_toSet v₀ v₀
          (fun i _ _ _ => i.isPrime)] at hsub
        obtain ⟨i, hi, hle⟩ := hsub
        exact hJ_not_le i (Finset.mem_coe.mp hi) hle
    obtain ⟨a, ha_eq⟩ : IsLocalization.IsInteger (𝓞 K)
        (algebraMap (𝓞 K) K b * ((x : Kˣ) : K)) := hb_in_J
    have ha_avoid : ∀ v ∈ S, a ∉ v.asIdeal := by
      intro v hv ha_mem
      have hb_mem_or : b ∈ v.asIdeal := by
        by_contra hb_not_mem
        have hv_b : v.intValuation b = 1 :=
          IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr
            hb_not_mem
        have hv_a : v.intValuation a ≠ 1 :=
          (IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.not.mpr
            (not_not.mpr ha_mem))
        have hmul : v.valuation K (algebraMap _ K a) =
            v.valuation K (algebraMap _ K b) *
              v.valuation K ((x : Kˣ) : K) := by
          rw [ha_eq, map_mul]
        rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
          IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
          hv_b, hα_val v ((hS_mem v).mp hv), mul_one] at hmul
        exact hv_a hmul
      exact hb_avoid v hv hb_mem_or
    have isUnit_of_avoid : ∀ r : 𝓞 K, (∀ v ∈ S, r ∉ v.asIdeal) →
        IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) r) := by
      intro r hr
      have hsup : Ideal.span {r} ⊔ (m.finitePart : Ideal (𝓞 K)) = ⊤ := by
        by_contra hne
        obtain ⟨M, hMmax, hle⟩ := Ideal.exists_le_maximal _ hne
        have hIM : (m.finitePart : Ideal (𝓞 K)) ≤ M :=
          le_trans le_sup_right hle
        have hMbot : M ≠ ⊥ := by
          intro hM
          rw [hM] at hIM
          exact hI (le_antisymm hIM bot_le)
        let P : IsDedekindDomain.HeightOneSpectrum (𝓞 K) :=
          IsDedekindDomain.HeightOneSpectrum.ofPrime
            (Ideal.prime_of_isPrime hMbot hMmax.isPrime)
        have hrM : r ∈ M :=
          hle (Submodule.mem_sup_left (Ideal.mem_span_singleton_self r))
        have hPmem : P ∈ S := (hS_mem P).mpr hIM
        exact hr P hPmem hrM
      rw [Ideal.eq_top_iff_one] at hsup
      obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hsup
      obtain ⟨c, hc⟩ := (Ideal.mem_span_singleton).mp hx
      have key : Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) r *
          Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) c = 1 := by
        have h3 : Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K))
            (r * c + y) = 1 := by
          rw [← hc, hxy]
          simp
        simpa only [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hy, add_zero,
          map_mul] using h3
      exact IsUnit.of_mul_eq_one _ key
    refine ⟨a, b, isUnit_of_avoid a ha_avoid, isUnit_of_avoid b hb_avoid, ?_⟩
    have hb_ne : algebraMap (𝓞 K) K b ≠ 0 := by
      intro h
      have hb0 : b = 0 :=
        IsFractionRing.injective (𝓞 K) K (by rw [h, map_zero])
      have h0 : Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) b = 0 := by
        rw [hb0, map_zero]
      exact (isUnit_of_avoid b hb_avoid).ne_zero h0
    rw [ha_eq]
    exact mul_div_cancel_left₀ _ hb_ne

/-- Equal fractions over `K` give equal finite-quotient units. -/
theorem quotientUnits_div_eq_of_div_eq
    (m : Modulus K) (a b c d : 𝓞 K)
    (ha : IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) a))
    (hb : IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) b))
    (hc : IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) c))
    (hd : IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) d))
    (h : algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b =
      algebraMap (𝓞 K) K c / algebraMap (𝓞 K) K d) :
    ha.unit * hb.unit⁻¹ = hc.unit * hd.unit⁻¹ := by
  classical
  by_cases htriv : Subsingleton (𝓞 K ⧸ (m.finitePart : Ideal (𝓞 K)))
  · let _ : Subsingleton (𝓞 K ⧸ (m.finitePart : Ideal (𝓞 K))) := htriv
    exact Subsingleton.elim _ _
  · rw [not_subsingleton_iff_nontrivial] at htriv
    let _ : Nontrivial (𝓞 K ⧸ (m.finitePart : Ideal (𝓞 K))) := htriv
    have hbK : algebraMap (𝓞 K) K b ≠ 0 := by
      intro h0
      have hb0 : b = 0 :=
        IsFractionRing.injective (𝓞 K) K (by rw [h0, map_zero])
      exact hb.ne_zero (by rw [hb0, map_zero])
    have hdK : algebraMap (𝓞 K) K d ≠ 0 := by
      intro h0
      have hd0 : d = 0 :=
        IsFractionRing.injective (𝓞 K) K (by rw [h0, map_zero])
      exact hd.ne_zero (by rw [hd0, map_zero])
    have hcross := (div_eq_div_iff hbK hdK).mp h
    have had : a * d = b * c :=
      IsFractionRing.injective (𝓞 K) K (by simp [map_mul, hcross, mul_comm])
    have hmk : Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) a *
        Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) d =
        Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) b *
          Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) c := by
      rw [← map_mul, ← map_mul, had]
    have hu : ha.unit * hd.unit = hc.unit * hb.unit := by
      apply Units.ext
      simp only [Units.val_mul, IsUnit.unit_spec]
      exact hmk.trans (mul_comm _ _)
    have h2 := congrArg (fun u => u * hb.unit⁻¹ * hd.unit⁻¹) hu
    simpa [mul_comm, mul_assoc, mul_left_comm] using h2

end Modulus
end NumberField
