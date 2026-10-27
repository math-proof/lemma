import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma X_sub_C_mul_eq_zero {T : Type u} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] {z : T} (hz : z ∈ maximalIdeal T) {g : PowerSeries T} (h : (PowerSeries.X - PowerSeries.C z) * g = 0) : g = 0 := by
  have hrec : ∀ n, PowerSeries.coeff n g = z * PowerSeries.coeff (n + 1) g := by
    intro n
    have := congrArg (PowerSeries.coeff (n + 1)) h
    rw [sub_mul, map_sub, PowerSeries.coeff_succ_X_mul, ← PowerSeries.smul_eq_C_mul, PowerSeries.coeff_smul, map_zero, sub_eq_zero] at this
    rw [this, smul_eq_mul]
  have hpow : ∀ k n, PowerSeries.coeff n g = z ^ k * PowerSeries.coeff (n + k) g := by
    intro k
    induction k
    ·
      intro n
      simp
    ·
      rename_i k ih
      intro n
      rw [ih n, hrec (n + k), pow_succ, mul_assoc, show n + k + 1 = n + (k + 1) by omega]
  ext n
  rw [map_zero]
  have hmem : PowerSeries.coeff n g ∈ ⨅ k : ℕ, maximalIdeal T ^ k := by
    rw [Ideal.mem_iInf]
    intro k
    rw [hpow k n]
    apply Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hz k)
  rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal T).ne_top, Ideal.mem_bot] at hmem
private lemma prod_mul_eq_zero {T : Type u} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] (S : Finset ι) (z : ι → T) (hz : ∀ i ∈ S, z i ∈ maximalIdeal T) {g : PowerSeries T} (h : (∏ i ∈ S, (PowerSeries.X - PowerSeries.C (z i))) * g = 0) : g = 0 := by
  classical
  induction S using Finset.induction_on generalizing g
  · simpa using h
  ·
    rename_i a s ha ih
    rw [Finset.prod_insert ha, mul_assoc] at h
    have h1 := X_sub_C_mul_eq_zero (hz a (Finset.mem_insert_self a s)) h
    refine ih (fun i hi => hz i (Finset.mem_insert_of_mem hi)) h1
/--
[PowerSeries_exists_isUnit_mul_eq_prod_X_sub_C_of_span_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_PowerSeries_exists_isUnit_mul_eq_prod_X_sub_C_of_span_eq.lean)
-/
@[path]
private lemma main
  {T : Type u} [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
  (S : Finset ι) (z : ι → T)
  (hz : ∀ i ∈ S, z i ∈ IsLocalRing.maximalIdeal T) (x : PowerSeries T)
  (h : Ideal.span {x} = Ideal.span {∏ i ∈ S, (PowerSeries.X - PowerSeries.C (z i))}) :
  -- imply
  ∃ u : PowerSeries T, IsUnit u ∧ u * x = ∏ i ∈ S, (PowerSeries.X - PowerSeries.C (z i)) := by
  -- proof
  set p := ∏ i ∈ S, (PowerSeries.X - PowerSeries.C (z i)) with hp
  have hx : x ∈ Ideal.span {p} := h ▸ Ideal.mem_span_singleton_self x
  have hpx : p ∈ Ideal.span {x} := h.symm ▸ Ideal.mem_span_singleton_self p
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hx
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hpx
  have hzero : p * (1 - b * a) = 0 := by
    have : p = b * a * p := by rw [mul_assoc, ha, hb]
    linear_combination this
  have hba : b * a = 1 := by
    have := prod_mul_eq_zero S z hz (by rw [hp] at hzero; apply hzero)
    refine (sub_eq_zero.mp this).symm
  refine ⟨b, IsUnit.of_mul_eq_one a hba, hb⟩


-- created on 2026-10-20
