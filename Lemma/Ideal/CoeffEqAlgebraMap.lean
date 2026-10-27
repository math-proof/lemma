import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[LaurentSeries_forall_coeff_mem_map_maximalIdeal_of_mul_eq_C_of_forall_coeff_mem_range_of_isUnit_coeff_order](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LaurentSeries_forall_coeff_mem_map_maximalIdeal_of_mul_eq_C_of_forall_coeff_mem_range_of_isUnit_coeff_order.lean)
-/
@[path]
private lemma main
  (A L : Type) [CommRing A] [Field L] [Algebra A L] (hinj : Function.Injective (algebraMap A L))
  (I : Ideal A)
  (Y Z : LaurentSeries L) (n₀ : ℤ) (c : A)
  (hZA : ∀ n : ℤ, ∃ a : A, Z.coeff n = algebraMap A L a)
  (hZ0 : ∀ n : ℤ, n < n₀ → Z.coeff n = 0)
  (hZu : ∃ u : A, IsUnit u ∧ Z.coeff n₀ = algebraMap A L u)
  (hYZ : Y * Z = HahnSeries.C (algebraMap A L c))
  (hc : c ∈ I) :
  -- imply
  ∀ n : ℤ, ∃ a ∈ I, Y.coeff n = algebraMap A L a := by
  -- proof
  classical
  obtain ⟨u, hu, hZn₀⟩ := hZu
  let _ : Nontrivial A := ⟨⟨0, 1, fun h => zero_ne_one (α := L) (by rw [← map_zero (algebraMap A L), h, map_one])⟩⟩
  have hu0 : algebraMap A L u ≠ 0 := by
    intro h
    apply hu.ne_zero (hinj (by rw [h, map_zero]))
  have hZne : Z ≠ 0 := by
    intro h
    apply hu0
    rw [← hZn₀, h, HahnSeries.coeff_zero]
  have hord : Z.order = n₀ := by
    apply le_antisymm
    ·
      have : Z.coeff n₀ ≠ 0 := by
        rw [hZn₀]
        apply hu0
      apply HahnSeries.order_le_of_coeff_ne_zero this
    ·
      by_contra h
      push Not at h
      apply (HahnSeries.coeff_order_eq_zero.not.mpr) hZne (hZ0 _ h)
  choose za hza using hZA
  let PA : PowerSeries A := PowerSeries.mk fun k => za (n₀ + (k : ℤ))
  have hPA : PA.map (algebraMap A L) = Z.powerSeriesPart := by
    ext k
    rw [PowerSeries.coeff_map, LaurentSeries.powerSeriesPart_coeff, hord, PowerSeries.coeff_mk, hza]
  have hPA0 : PA.constantCoeff = u := by
    apply hinj
    rw [← hZn₀, hza n₀, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
    simp
  let QA : PowerSeries A := PA.invOfUnit hu.unit
  have hPQ : PA * QA = 1 := PowerSeries.mul_invOfUnit PA hu.unit (by rw [hPA0, IsUnit.unit_spec])
  have hPQL : Z.powerSeriesPart * QA.map (algebraMap A L) = 1 := by
    rw [← hPA, ← RingHom.map_mul, hPQ, RingHom.map_one]
  set W : LaurentSeries L := HahnSeries.single (-n₀) (1 : L) * HahnSeries.ofPowerSeries ℤ L (QA.map (algebraMap A L)) with hWdef
  have hZW : Z * W = 1 := by
    have hZ := LaurentSeries.single_order_mul_powerSeriesPart Z
    rw [hord] at hZ
    rw [← hZ, hWdef]
    calc
      _ = (HahnSeries.single n₀ (1 : L) * HahnSeries.single (-n₀) (1 : L)) * (HahnSeries.ofPowerSeries ℤ L Z.powerSeriesPart * HahnSeries.ofPowerSeries ℤ L (QA.map (algebraMap A L))) := by ring
      _ = 1 := by
        rw [HahnSeries.single_mul_single, add_neg_cancel, one_mul, ← RingHom.map_mul, hPQL, RingHom.map_one, mul_one, HahnSeries.single_zero_one]
  have hY : Y = HahnSeries.C (algebraMap A L c) * W := by
    rw [← mul_one Y, ← hZW, ← mul_assoc, hYZ]
  have hWcoef : ∀ n : ℤ, ∃ a : A, W.coeff n = algebraMap A L a := by
    intro n
    rw [hWdef, HahnSeries.coeff_single_mul, one_mul]
    obtain hm | hm := le_or_gt 0 (n - -n₀)
    ·
      obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hm
      rw [hk, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]
      exact ⟨_, rfl⟩
    ·
      refine ⟨0, ?_⟩
      rw [map_zero, HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_of_notMem_range]
      intro hmem
      obtain ⟨k, hk⟩ := hmem
      change (k : ℤ) = _ at hk
      omega
  intro n
  obtain ⟨a, ha⟩ := hWcoef n
  refine ⟨c * a, I.mul_mem_right _ hc, ?_⟩
  rw [hY, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, ha, smul_eq_mul, map_mul]


-- created on 2026-10-20
