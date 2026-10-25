/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part5
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeber
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.IdealFactorization
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.FinitePlaceAbsValue
import Theorem.v1.Atlas.NumberTheoryI.code.IdealFactorization.Part3
import Theorem.v1.Atlas.NumberTheoryI.code.FinitePlaceAbsValue
import Def.v1.Atlas.NumberTheoryI.code.RayClassFields.Part22


noncomputable section

open scoped NumberField

namespace RayClassField

variable {K : Type*} [Field K] [NumberField K]

universe u

attribute [instance] instFintypeSignsTimesUnits

theorem coprime_rep_exists (𝔪 : @Modulus K _ _)
    (α : UnitsCoprime_subgroup' K 𝔪) :
    ∃ (a b : NumberField.RingOfIntegers K),
      IsUnit (Ideal.Quotient.mk 𝔪.finitePartIdeal a) ∧
      IsUnit (Ideal.Quotient.mk 𝔪.finitePartIdeal b) ∧
      algebraMap (NumberField.RingOfIntegers K) K a /
        algebraMap (NumberField.RingOfIntegers K) K b = ((α : Kˣ) : K) := by
  classical

  by_cases htriv : Subsingleton (NumberField.RingOfIntegers K ⧸ 𝔪.finitePartIdeal)
  · obtain ⟨a₀, b₀, hb₀, hab₀⟩ := IsFractionRing.div_surjective
      (NumberField.RingOfIntegers K) ((α : Kˣ) : K)
    haveI := htriv
    refine ⟨a₀, b₀, isUnit_of_subsingleton _, isUnit_of_subsingleton _, ?_⟩
    rw [← hab₀]
  ·
    rw [not_subsingleton_iff_nontrivial] at htriv; haveI := htriv

    obtain ⟨a₀, b₀, hb₀_mem, hab₀⟩ := IsFractionRing.div_surjective
      (NumberField.RingOfIntegers K) ((α : Kˣ) : K)

    have hα_ne : ((α : Kˣ) : K) ≠ 0 := Units.ne_zero (α : Kˣ)

    have hα_val : ∀ v : FinitePlace K, 𝔪 (Place.finite v) ≠ 0 →
        v.valuation K ((α : Kˣ) : K) = 1 := α.2

    set T := (𝔪.finite_support.preimage (f := Place.finite)
      (fun a _ b _ hab => by cases hab; rfl)).toFinset with hT_def
    have hT_mem : ∀ v : FinitePlace K, v ∈ T ↔ 𝔪 (Place.finite v) ≠ 0 := by
      intro v; simp [hT_def, Set.Finite.mem_toFinset]

    have hT_nonempty : T.Nonempty := by
      by_contra h_empty
      rw [Finset.not_nonempty_iff_eq_empty] at h_empty
      have hI_top : 𝔪.finitePartIdeal = ⊤ := by
        show T.prod (fun 𝔭 => 𝔭.asIdeal ^ 𝔪 (Place.finite 𝔭)) = ⊤
        simp [h_empty, Ideal.one_eq_top]
      exact absurd (Ideal.Quotient.nontrivial_iff.mp inferInstance) (not_not.mpr hI_top)

    let J : Ideal (NumberField.RingOfIntegers K) :=
    { carrier := {b | IsLocalization.IsInteger (NumberField.RingOfIntegers K)
        (algebraMap (NumberField.RingOfIntegers K) K b * ((α : Kˣ) : K))}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, IsLocalization.IsInteger, map_add, add_mul] at *
        obtain ⟨ca, hca⟩ := ha; obtain ⟨cb, hcb⟩ := hb
        exact ⟨ca + cb, by rw [map_add, hca, hcb]⟩
      zero_mem' := by
        simp only [Set.mem_setOf_eq, map_zero, zero_mul]; exact ⟨0, map_zero _⟩
      smul_mem' := fun c {b} hb => by
        simp only [Set.mem_setOf_eq, IsLocalization.IsInteger, smul_eq_mul, map_mul,
                   mul_assoc] at *
        obtain ⟨cb, hcb⟩ := hb; exact ⟨c * cb, by rw [map_mul, hcb]⟩ }

    have hb₀_in_J : b₀ ∈ J := by
      show IsLocalization.IsInteger _ _
      rw [← hab₀, mul_div_cancel₀]
      · exact ⟨a₀, rfl⟩
      · exact map_ne_zero_of_mem_nonZeroDivisors _
          (IsFractionRing.injective (NumberField.RingOfIntegers K) K) hb₀_mem

    have hJ_ne_bot : J ≠ ⊥ := by
      intro h
      have : b₀ ∈ (⊥ : Ideal (NumberField.RingOfIntegers K)) := h ▸ hb₀_in_J
      rw [Ideal.mem_bot] at this
      exact hα_ne (by rw [← hab₀]; simp [this])

    have hJ_not_le : ∀ v ∈ T, ¬(J ≤ v.asIdeal) := by
      intro v hv hle
      have hv_ne := (hT_mem v).mp hv
      have hv_ne_top : v.asIdeal ≠ ⊤ := v.isPrime.ne_top


      obtain ⟨c, hc_int, i, hi_mem, hc_notmem⟩ := Ideal.exist_integer_multiples_notMem (K := K)
        hv_ne_top ({0, 1} : Finset (Fin 2)) (fun i => if i = 0 then ((α : Kˣ) : K) else 1)
        (j := 1) (by simp) (by simp)

      have hc_is_int : IsLocalization.IsInteger (NumberField.RingOfIntegers K) c := by
        have := hc_int 1 (by simp); simpa using this

      have hcα_is_int : IsLocalization.IsInteger (NumberField.RingOfIntegers K)
          (c * ((α : Kˣ) : K)) := by
        have := hc_int 0 (by simp); simpa using this

      obtain ⟨b_int, hb_int⟩ := hc_is_int

      have hb_int_in_J : b_int ∈ J := by
        show IsLocalization.IsInteger _ _; rw [hb_int]; exact hcα_is_int

      have hb_int_mem : b_int ∈ v.asIdeal := hle hb_int_in_J

      have hv_c_ne1 : v.valuation K c ≠ 1 := by
        rw [← hb_int, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
        rw [Ne, IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
        exact not_not.mpr hb_int_mem

      have hv_α_eq1 : v.valuation K ((α : Kˣ) : K) = 1 := hα_val v hv_ne

      have hv_cα_ne1 : v.valuation K (c * ((α : Kˣ) : K)) ≠ 1 := by
        rw [map_mul, hv_α_eq1, mul_one]; exact hv_c_ne1

      obtain ⟨a_int, ha_int⟩ := hcα_is_int

      have ha_int_mem : a_int ∈ v.asIdeal := by
        rw [← not_not (a := a_int ∈ v.asIdeal)]
        rw [← IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
        intro h_eq
        exact hv_cα_ne1 (by
          rw [← ha_int, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, h_eq])


      rcases i with ⟨i, hi⟩
      interval_cases i
      ·
        simp only [Fin.mk_zero] at hc_notmem
        simp only [ite_true] at hc_notmem
        exact hc_notmem ((FractionalIdeal.mem_coeIdeal _).mpr ⟨a_int, ha_int_mem, ha_int⟩)
      ·
        simp only [Fin.mk_one, one_ne_zero, ite_false, mul_one] at hc_notmem
        exact hc_notmem ((FractionalIdeal.mem_coeIdeal _).mpr ⟨b_int, hb_int_mem, hb_int⟩)

    have ⟨b, hb_in_J, hb_avoid⟩ : ∃ b ∈ J, ∀ v ∈ T, b ∉ v.asIdeal := by
      by_contra h
      push_neg at h
      have hsub : (J : Set (NumberField.RingOfIntegers K)) ⊆
          ⋃ v ∈ (↑T : Set (FinitePlace K)), (v.asIdeal : Set _) := by
        intro x hx; obtain ⟨v, hv, hvx⟩ := h x hx
        exact Set.mem_biUnion (Finset.mem_coe.mpr hv) hvx
      obtain ⟨v₀, hv₀⟩ := hT_nonempty
      rw [Ideal.subset_union_prime_finite T.finite_toSet v₀ v₀
        (fun i _ _ _ => i.isPrime)] at hsub
      obtain ⟨i, hi, hle⟩ := hsub
      exact hJ_not_le i (Finset.mem_coe.mp hi) hle

    obtain ⟨a, ha_eq⟩ : IsLocalization.IsInteger (NumberField.RingOfIntegers K)
        (algebraMap (NumberField.RingOfIntegers K) K b * ((α : Kˣ) : K)) := hb_in_J

    have ha_avoid : ∀ v ∈ T, a ∉ v.asIdeal := by
      intro v hv ha_mem
      have hb_mem_or : b ∈ v.asIdeal := by
        by_contra hb_not_mem

        have hv_b : v.intValuation b = 1 :=
          IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr hb_not_mem

        have hv_a : v.intValuation a ≠ 1 :=
          (IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.not.mpr (not_not.mpr ha_mem))

        have : v.valuation K (algebraMap _ K a) = v.valuation K (algebraMap _ K b) *
            v.valuation K ((α : Kˣ) : K) := by
          rw [ha_eq, map_mul]
        rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
            IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
            hv_b, hα_val v ((hT_mem v).mp hv), mul_one] at this
        exact hv_a this
      exact hb_avoid v hv hb_mem_or

    have isUnit_of_avoid : ∀ (r : NumberField.RingOfIntegers K),
        (∀ v ∈ T, r ∉ v.asIdeal) →
        IsUnit (Ideal.Quotient.mk 𝔪.finitePartIdeal r) := by
      intro r hr

      show IsUnit (Ideal.Quotient.mk
        (T.prod (fun 𝔭 => 𝔭.asIdeal ^ 𝔪 (Place.finite 𝔭))) r)

      have h1 : ∀ v ∈ T, Ideal.span {r} ⊔ (v.asIdeal ^ 𝔪 (Place.finite v)) = ⊤ := by
        intro v hv
        have hsup : Ideal.span {r} ⊔ v.asIdeal = ⊤ := by
          rw [Ideal.eq_top_iff_one]
          obtain ⟨y, i, hi, hyi⟩ := Ideal.IsMaximal.exists_inv v.isMaximal (hr v hv)
          exact Submodule.mem_sup.mpr
            ⟨y * r, Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self r), i, hi, hyi⟩
        exact Ideal.sup_pow_eq_top hsup

      have h2 : Ideal.span {r} ⊔ T.prod (fun v => v.asIdeal ^ 𝔪 (Place.finite v)) = ⊤ :=
        Ideal.sup_prod_eq_top h1
      rw [Ideal.eq_top_iff_one] at h2
      obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp h2
      rw [Ideal.mem_span_singleton] at hx; obtain ⟨c, rfl⟩ := hx
      have key : Ideal.Quotient.mk (T.prod (fun v => v.asIdeal ^ 𝔪 (Place.finite v))) r *
          Ideal.Quotient.mk (T.prod (fun v => v.asIdeal ^ 𝔪 (Place.finite v))) c = 1 := by
        have h3 : Ideal.Quotient.mk (T.prod (fun v => v.asIdeal ^ 𝔪 (Place.finite v)))
            (r * c + y) = 1 := by rw [hxy]; simp
        rwa [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hy, add_zero, map_mul] at h3
      exact isUnit_of_mul_eq_one
        (b := Ideal.Quotient.mk (T.prod (fun v => v.asIdeal ^ 𝔪 (Place.finite v))) c) key

    refine ⟨a, b, isUnit_of_avoid a ha_avoid, isUnit_of_avoid b hb_avoid, ?_⟩

    have hb_ne : algebraMap (NumberField.RingOfIntegers K) K b ≠ 0 := by
      intro h
      have hb_zero : b = 0 := by
        rwa [map_eq_zero_iff _ (IsFractionRing.injective (NumberField.RingOfIntegers K) K)] at h
      obtain ⟨v₀, hv₀⟩ := hT_nonempty
      exact hb_avoid v₀ hv₀ (hb_zero ▸ v₀.asIdeal.zero_mem)
    rw [ha_eq, mul_div_cancel_left₀ _ hb_ne]

end RayClassField
end
