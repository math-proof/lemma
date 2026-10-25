/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/FiniteCongruence.lean -/

import Theorem.NumberTheory.NumberField.RayClass.RayGroup.Part3
import Lemma.Nat.NumberField.RayClass.RayGroup
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.FractionalIdeal.Operations
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

/-- Private bridge: for `x ≠ 0`, the `v`-adic valuation is `exp (-count)`. -/
theorem valuation_eq_exp_neg_count
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) :
    v.valuation K x = WithZero.exp
      (-FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)) := by
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq (𝓞 K)⁰ x
  have hr : r ≠ 0 := fun h => hx (by simp [h])
  have hs0 : (s : 𝓞 K) ≠ 0 := nonZeroDivisors.ne_zero s.property
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_mk',
    v.intValuation_if_neg hr, v.intValuation_if_neg hs0, ← WithZero.exp_sub]
  congr 1
  have hI : FractionalIdeal.spanSingleton (𝓞 K)⁰
      (IsLocalization.mk' K r s) ≠ 0 := by
    rw [ne_eq, FractionalIdeal.spanSingleton_eq_zero_iff]
    exact hx
  have hrep : FractionalIdeal.spanSingleton (𝓞 K)⁰ (IsLocalization.mk' K r s)
      = FractionalIdeal.spanSingleton (𝓞 K)⁰ ((algebraMap (𝓞 K) K) s)⁻¹ *
        ((Ideal.span {r} : Ideal (𝓞 K)) :
          FractionalIdeal (𝓞 K)⁰ K) := by
    rw [FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton]
    congr 1
    rw [IsFractionRing.mk'_eq_div, div_eq_inv_mul]
  rw [FractionalIdeal.count_well_defined K v hI hrep]
  ring

/-- Count bound for a sum of two generators with nonzero sum.

Only the nonzero-sum guard is required publicly; zero summands are handled
by reduction to the other summand. -/
theorem count_spanSingleton_add_ge_of_ne_zero
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {x y : K} {n : ℤ} (hxy : x + y ≠ 0)
    (hx : n ≤ FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ x))
    (hy : n ≤ FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ y)) :
    n ≤ FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x + y)) := by
  by_cases hxx : x = 0
  · subst hxx
    rw [zero_add] at hxy ⊢
    have h0 : FractionalIdeal.spanSingleton (𝓞 K)⁰ (0 : K) = 0 :=
      FractionalIdeal.spanSingleton_zero
    rw [h0, FractionalIdeal.count_zero] at hx
    omega
  · by_cases hyy : y = 0
    · subst hyy
      rw [add_zero] at hxy ⊢
      have h0 : FractionalIdeal.spanSingleton (𝓞 K)⁰ (0 : K) = 0 :=
        FractionalIdeal.spanSingleton_zero
      rw [h0, FractionalIdeal.count_zero] at hy
      omega
    · have evx := valuation_eq_exp_neg_count v hxx
      have evy := valuation_eq_exp_neg_count v hyy
      have evxy := valuation_eq_exp_neg_count v hxy
      have hvx : v.valuation K x ≤ WithZero.exp (-n) := by
        rw [evx, WithZero.exp_le_exp]
        omega
      have hvy : v.valuation K y ≤ WithZero.exp (-n) := by
        rw [evy, WithZero.exp_le_exp]
        omega
      have hadd := Valuation.map_add (v.valuation K) x y
      have hle : v.valuation K (x + y) ≤ WithZero.exp (-n) :=
        le_trans hadd (max_le hvx hvy)
      rw [evxy, WithZero.exp_le_exp] at hle
      omega

/-- A member of `rayElements m` has principal fractional-ideal count zero
at every finite prime supported by `m`. -/
theorem rayElement_count_spanSingleton_eq_zero
    (m : Modulus K) (x : Kˣ)
    (hx : x ∈ rayElements m)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hv : finiteSupported m v) :
    FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)) = 0 := by
  have h := (mem_rayElements_iff m x).mp hx
  rw [mem_coprimeFractionalIdeals_iff] at h
  have h0 := h v hv
  rwa [coe_toPrincipalIdeal] at h0

/-- A ray element has valuation one at every finite prime supported by the modulus.
Source (N406 §21.3): the supported-finite-place fact; compare
[`valuation_eq_one_of_spanSingleton_coprime'`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L1206-L1248)
and `hx_coprime`. -/
theorem rayElement_valuation_eq_one
    (m : Modulus K) (x : rayElements m)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hv : finiteSupported m v) :
    v.valuation K (((x : Kˣ) : K)) = 1 := by
  rw [valuation_eq_exp_neg_count v (Units.ne_zero (x : Kˣ)),
    rayElement_count_spanSingleton_eq_zero m (x : Kˣ) x.property v hv,
    neg_zero, WithZero.exp_zero]

/-- Valuation-one criterion for ray elements: if the normalized valuation of `a`
is one at every finite prime supported by `m`, then the principal fractional
ideal `(a)` has count zero at each such prime, so `a ∈ rayElements m`.

This is the converse of `rayElement_valuation_eq_one`: the converse valuation
criterion used to turn the controlled approximation witness into a ray element.
It is a reusable bridge toward N406, not itself the full source theorem. -/
theorem mem_rayElements_of_valuation_eq_one
    (m : Modulus K) (a : Kˣ)
    (h : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      finiteSupported m v → v.valuation K ((a : K)) = 1) :
    a ∈ rayElements m := by
  rw [mem_rayElements_iff, mem_coprimeFractionalIdeals_iff]
  intro v hv
  rw [coe_toPrincipalIdeal]
  have hne : (a : K) ≠ 0 := Units.ne_zero a
  have hev := valuation_eq_exp_neg_count v hne
  have hval := h v hv
  rw [hev, ← WithZero.exp_zero] at hval
  have hcount := WithZero.exp_inj.mp hval
  omega

/-- Congruence at the finite part is closed under multiplication. -/
theorem CongruentOneAtFinitePart.mul
    {m : Modulus K} {x y : Kˣ}
    (hx : CongruentOneAtFinitePart m x)
    (hy : CongruentOneAtFinitePart m y)
    (hmem : x ∈ rayElements m) :
    CongruentOneAtFinitePart m (x * y) := by
  intro v hv
  by_cases hxy : ((x * y : Kˣ) : K) = 1
  · exact Or.inl hxy
  · by_cases hxx : (x : K) = 1
    · have hval : ((x * y : Kˣ) : K) = (y : K) := by
        simp [Units.val_mul, hxx]
      have hsub : ((x * y : Kˣ) : K) - 1 = (y : K) - 1 := by rw [hval]
      rcases hy v hv with h | h
      · exact Or.inl (by rw [hval, h])
      · exact Or.inr (by rwa [hsub])
    · by_cases hyy : (y : K) = 1
      · have hval : ((x * y : Kˣ) : K) = (x : K) := by
          simp [Units.val_mul, hyy]
        have hsub : ((x * y : Kˣ) : K) - 1 = (x : K) - 1 := by rw [hval]
        rcases hx v hv with h | h
        · exact absurd h hxx
        · exact Or.inr (by rwa [hsub])
      · rcases hx v hv with h | hbx
        · exact absurd h hxx
        · rcases hy v hv with h | hby
          · exact absurd h hyy
          · have hcx := rayElement_count_spanSingleton_eq_zero
              m x hmem v hv
            have hsuby : (y : K) - 1 ≠ 0 := sub_ne_zero.mpr hyy
            have hIx : FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) ≠ 0 := by
              rw [ne_eq, FractionalIdeal.spanSingleton_eq_zero_iff]
              exact Units.ne_zero x
            have hIy : FractionalIdeal.spanSingleton (𝓞 K)⁰
                ((y : K) - 1) ≠ 0 := by
              rw [ne_eq, FractionalIdeal.spanSingleton_eq_zero_iff]
              exact hsuby
            have hmul : FractionalIdeal.spanSingleton (𝓞 K)⁰
                ((x : K) * ((y : K) - 1)) =
                FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) *
                  FractionalIdeal.spanSingleton (𝓞 K)⁰ ((y : K) - 1) :=
              (FractionalIdeal.spanSingleton_mul_spanSingleton _ _).symm
            have hcmul : FractionalIdeal.count K v
                (FractionalIdeal.spanSingleton (𝓞 K)⁰
                  ((x : K) * ((y : K) - 1))) =
                FractionalIdeal.count K v
                  (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)) +
                FractionalIdeal.count K v
                  (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((y : K) - 1)) := by
              rw [hmul, FractionalIdeal.count_mul K v hIx hIy]
            have hbmul : finiteExponent m v ≤ FractionalIdeal.count K v
                (FractionalIdeal.spanSingleton (𝓞 K)⁰
                  ((x : K) * ((y : K) - 1))) := by
              rw [hcmul, hcx, zero_add]
              exact hby
            have hid : (x : K) * ((y : K) - 1) + ((x : K) - 1) =
                ((x * y : Kˣ) : K) - 1 := by
              simp only [Units.val_mul]
              ring
            have hsum : (x : K) * ((y : K) - 1) + ((x : K) - 1) ≠ 0 := by
              rw [hid]
              exact sub_ne_zero.mpr hxy
            have hfin := count_spanSingleton_add_ge_of_ne_zero
              v hsum hbmul hbx
            rw [hid] at hfin
            exact Or.inr hfin

/-- Congruence at the finite part is closed under inversion. -/
theorem CongruentOneAtFinitePart.inv
    {m : Modulus K} {x : Kˣ}
    (hx : CongruentOneAtFinitePart m x)
    (hmem : x ∈ rayElements m) :
    CongruentOneAtFinitePart m x⁻¹ := by
  intro v hv
  by_cases hinv : ((x⁻¹ : Kˣ) : K) = 1
  · exact Or.inl hinv
  · by_cases hxx : (x : K) = 1
    · exfalso
      exact hinv (by simp [Units.val_inv_eq_inv_val, hxx])
    · rcases hx v hv with h | hbx
      · exact absurd h hxx
      · have hcx := rayElement_count_spanSingleton_eq_zero
          m x hmem v hv
        have hsub : (x : K) - 1 ≠ 0 := sub_ne_zero.mpr hxx
        have hsubinv : ((x⁻¹ : Kˣ) : K) - 1 ≠ 0 := sub_ne_zero.mpr hinv
        have hxne : (x : K) ≠ 0 := Units.ne_zero x
        have hI1 : FractionalIdeal.spanSingleton (𝓞 K)⁰
            (((x⁻¹ : Kˣ) : K) - 1) ≠ 0 := by
          rw [ne_eq, FractionalIdeal.spanSingleton_eq_zero_iff]
          exact hsubinv
        have hIx : FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) ≠ 0 := by
          rw [ne_eq, FractionalIdeal.spanSingleton_eq_zero_iff]
          exact hxne
        have hid : (((x⁻¹ : Kˣ) : K) - 1) * (x : K) = -((x : K) - 1) := by
          rw [Units.val_inv_eq_inv_val]
          field_simp
          ring
        have hmul : FractionalIdeal.spanSingleton (𝓞 K)⁰
            (((x⁻¹ : Kˣ) : K) - 1) *
            FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) =
            FractionalIdeal.spanSingleton (𝓞 K)⁰ (-((x : K) - 1)) := by
          rw [FractionalIdeal.spanSingleton_mul_spanSingleton, hid]
        have hcmul : FractionalIdeal.count K v
            (FractionalIdeal.spanSingleton (𝓞 K)⁰ (-((x : K) - 1))) =
            FractionalIdeal.count K v
              (FractionalIdeal.spanSingleton (𝓞 K)⁰
                (((x⁻¹ : Kˣ) : K) - 1)) +
            FractionalIdeal.count K v
              (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)) := by
          rw [← hmul, FractionalIdeal.count_mul K v hI1 hIx]
        have hneg : FractionalIdeal.spanSingleton (𝓞 K)⁰ (-((x : K) - 1)) =
            FractionalIdeal.spanSingleton (𝓞 K)⁰ ((x : K) - 1) := by
          apply le_antisymm
          · rw [FractionalIdeal.spanSingleton_le_iff_mem,
              FractionalIdeal.mem_spanSingleton]
            exact ⟨-1, by simp⟩
          · rw [FractionalIdeal.spanSingleton_le_iff_mem,
              FractionalIdeal.mem_spanSingleton]
            exact ⟨-1, by simp⟩
        rw [hneg, hcx, add_zero] at hcmul
        exact Or.inr (by omega)

end Modulus
end NumberField
