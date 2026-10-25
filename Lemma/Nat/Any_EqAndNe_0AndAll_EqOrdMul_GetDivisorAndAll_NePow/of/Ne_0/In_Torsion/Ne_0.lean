import Mathlib
import sympy.Basic
import Lemma.AlgebraicCurve.DivisorClassGroup
open AlgebraicCurve


private lemma ord_algebraMap_aux {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (c : K) : v.ord (algebraMap K F c) = 0 := by
  if hc : c = 0 then
    simp [hc]
  else
    have hc' : algebraMap K F c ≠ 0 := (map_ne_zero _).mpr hc
    have hmem : algebraMap K F c ∈ v.toValuationSubring := v.algebraMap_mem' c
    have hmem' : (algebraMap K F c)⁻¹ ∈ v.toValuationSubring := by
      rw [← map_inv₀]; exact v.algebraMap_mem' c⁻¹
    let u : v.toValuationSubringˣ :=
      ⟨⟨_, hmem⟩, ⟨_, hmem'⟩,
        Subtype.ext (mul_inv_cancel₀ hc'),
        Subtype.ext (inv_mul_cancel₀ hc')⟩
    exact v.ord_coe_unit u

private lemma mk_eq_zero_iff_aux {K F : Type*} [Field K] [Field F] [Algebra K F] (D : Divisor.degZero (K := K) (F := F)) : Pic0.mk D = 0 ↔ Divisor.IsPrincipal (D : Divisor K F) := by
  rw [show Pic0.mk D = QuotientAddGroup.mk D from rfl, QuotientAddGroup.eq_zero_iff,
    AddSubgroup.mem_addSubgroupOf, Divisor.mem_principal]

private lemma ord_pow_aux {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (h : F) (n : ℕ) : v.ord (h ^ n) = n * v.ord h := by rw [← zpow_natCast]; exact v.ord_zpow h n 
private lemma mk_eq_zero_of_eq_algebraMap_mul_pow {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} (hn : n ≠ 0) {f : F} (hf : f ≠ 0) {D : Divisor.degZero (K := K) (F := F)} (hfD : ∀ v : Place K F, v.ord f = n * (D : Divisor K F) v) (c : K) (h : F) (hfch : f = algebraMap K F c * h ^ n) : Pic0.mk D = 0 := by
  have hne : algebraMap K F c ≠ 0 ∧ h ^ n ≠ 0 := mul_ne_zero_iff.mp (hfch ▸ hf)
  have hh : h ≠ 0 := fun h0 => hne.2 (by rw [h0]; exact zero_pow hn)
  rw [mk_eq_zero_iff_aux]
  refine ⟨h, hh, fun v => ?_⟩
  have h1 : v.ord f = n * v.ord h := by
    rw [hfch, v.ord_mul hne.1 hne.2, ord_algebraMap_aux, zero_add, ord_pow_aux]
  have h2 : (n : ℤ) * (D : Divisor K F) v = n * v.ord h := (hfD v).symm.trans h1
  refine mul_left_cancel₀ (Int.natCast_ne_zero.mpr hn) h2

private lemma ne_algebraMap_mul_pow_of_mk_ne_zero {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} (hn : n ≠ 0) {f : F} (hf : f ≠ 0) {D : Divisor.degZero (K := K) (F := F)} (hfD : ∀ v : Place K F, v.ord f = n * (D : Divisor K F) v) (hx : Pic0.mk D ≠ 0) (c : K) (h : F) : f ≠ algebraMap K F c * h ^ n :=
  fun hfch => hx (mk_eq_zero_of_eq_algebraMap_mul_pow hn hf hfD c h hfch)

private lemma exists_ord_eq_mul_of_mk_mem_torsion {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} {x : Pic0 K F} (hx : x ∈ Pic0.torsion K F n) {D : Divisor.degZero (K := K) (F := F)} (hD : Pic0.mk D = x) : ∃ f : F, f ≠ 0 ∧ ∀ v : Place K F, v.ord f = n * (D : Divisor K F) v := by
  have hx' : (n : ℤ) • x = 0 := Pic0.mem_torsion.mp hx
  have h1 : Pic0.mk ((n : ℤ) • D) = 0 := by
    have h2 : Pic0.mk ((n : ℤ) • D) = (n : ℤ) • Pic0.mk D := by
      show QuotientAddGroup.mk ((n : ℤ) • D) = (n : ℤ) • (QuotientAddGroup.mk D)
      exact QuotientAddGroup.mk_zsmul
        ((Divisor.principal (K := K) (F := F)).addSubgroupOf
          (Divisor.degZero (K := K) (F := F))) D (n : ℤ)
    rw [h2, hD, hx']
  have h3 : ((n : ℤ) • D : Divisor.degZero (K := K) (F := F)) ∈
    (Divisor.principal (K := K) (F := F)).addSubgroupOf
      (Divisor.degZero (K := K) (F := F)) :=
    (QuotientAddGroup.eq_zero_iff _).mp h1
  rw [AddSubgroup.mem_addSubgroupOf] at h3
  have h4 : Divisor.IsPrincipal ((n : ℤ) • (D : Divisor K F)) := Divisor.mem_principal.mp h3
  obtain ⟨f, hf0, hford⟩ := h4
  refine ⟨f, hf0, fun v => ?_⟩
  have := hford v
  rw [Finsupp.smul_apply, smul_eq_mul] at this
  apply this.symm
/--
[AlgebraicCurve_Pic0_exists_ord_eq_mul_and_forall_pow_ne_of_ne_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_Pic0_exists_ord_eq_mul_and_forall_pow_ne_of_ne_zero.lean)
-/
@[path]
private lemma main
  [Field K] [Field F] [Algebra K F]
  {n : ℕ}
  {x : Pic0 K F}
-- given
  (hn : n ≠ 0)
  (hx : x ∈ Pic0.torsion K F n)
  (hx0 : x ≠ 0) :
-- imply
  ∃ (D : Divisor.degZero (K :=
  K) (F := F)) (f : F),
  Pic0.mk D = x ∧ f ≠ 0 ∧ (∀ v : Place K F, v.ord f = n * (D : Divisor K F) v) ∧
    ∀ b : F, b ^ n ≠ f := by
-- proof
    obtain ⟨D, hD⟩ := Pic0.mk_surjective x
    obtain ⟨f, hf0, hfD⟩ := exists_ord_eq_mul_of_mk_mem_torsion hx hD
    refine ⟨D, f, hD, hf0, hfD, fun b hb => ?_⟩
    exact ne_algebraMap_mul_pow_of_mk_ne_zero hn hf0 hfD (hD ▸ hx0) 1 b
      (by rw [map_one, one_mul, hb])


-- created on 2026-10-23
