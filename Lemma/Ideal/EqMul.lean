import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[ValuationSubring_exists_units_eq_mul_of_algebraMap_adicCompletion_eq_mul_of_isUnit](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ValuationSubring_exists_units_eq_mul_of_algebraMap_adicCompletion_eq_mul_of_isUnit.lean)
-/
@[path]
private lemma main
  [Field L] (A : ValuationSubring L) (I : Ideal ↥A) (hI : I ≠ ⊤)
  (hsep : ∀ x : ↥A, (∀ n : ℕ, x ∈ I ^ n) → x = 0)
  (α β : ↥A) (u : Units (AdicCompletion I ↥A))
  (h : algebraMap ↥A (AdicCompletion I ↥A) α = algebraMap ↥A (AdicCompletion I ↥A) β * u) :
  -- imply
  ∃ v : Units ↥A, α = β * v := by
  -- proof
  classical
  have hIm : I ≤ IsLocalRing.maximalIdeal ↥A := IsLocalRing.le_maximalIdeal hI
  have hred : ∀ n : ℕ, 0 < n → ∃ w : ↥A, IsUnit w ∧ α - β * w ∈ I ^ n := by
    intro n hn
    obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n (u : AdicCompletion I ↥A))
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n (↑u⁻¹ : AdicCompletion I ↥A))
    have hwy : Ideal.Quotient.mk (I ^ n) (w * y) = 1 := by
      rw [map_mul, hw, hy, ← map_mul, Units.mul_inv, map_one]
    have hIn : I ^ n ≤ IsLocalRing.maximalIdeal ↥A := (Ideal.pow_le_self hn.ne').trans hIm
    have hwunit : IsUnit w := by
      have h1 : w * y - 1 ∈ I ^ n := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hwy, map_one, sub_self]
      have h2 : w * y - 1 ∈ IsLocalRing.maximalIdeal ↥A := hIn h1
      have h3 : IsUnit (w * y) := by
        by_contra hnu
        have hmem : w * y ∈ IsLocalRing.maximalIdeal ↥A := (IsLocalRing.mem_maximalIdeal _).mpr hnu
        have : (1 : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
          have this := Ideal.sub_mem _ hmem h2
          rw [sub_sub_cancel] at this
          refine this
        refine (IsLocalRing.maximalIdeal.isMaximal ↥A).ne_top (Ideal.eq_top_of_isUnit_mem _ this isUnit_one)
      refine isUnit_of_mul_isUnit_left h3
    refine ⟨w, hwunit, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hw, ← AdicCompletion.evalₐ_of, ← AdicCompletion.evalₐ_of,
      ← map_mul, ← map_sub]
    have hof : ∀ x : ↥A, AdicCompletion.of I ↥A x = algebraMap ↥A (AdicCompletion I ↥A) x := fun x => rfl
    rw [hof, hof, h, sub_self, map_zero]
  cases ValuationRing.dvd_total β α
  ·
    rename_i hdiv
    obtain ⟨t, ht⟩ := hdiv
    if htu : IsUnit t then
      refine ⟨htu.unit, ?_⟩
      rw [IsUnit.unit_spec]
      refine ht
    else
      have htm : t ∈ IsLocalRing.maximalIdeal ↥A := (IsLocalRing.mem_maximalIdeal _).mpr htu
      have hβ : β = 0 := by
        apply hsep
        intro n
        cases Nat.eq_zero_or_pos n
        ·
          rename_i hz
          rw [hz, pow_zero, Ideal.one_eq_top]
          refine Submodule.mem_top
        ·
          rename_i hn
          obtain ⟨w, hw, hmem⟩ := hred n hn
          have htw : IsUnit (t - w) := by
            by_contra hnu
            have h1 : t - w ∈ IsLocalRing.maximalIdeal ↥A := (IsLocalRing.mem_maximalIdeal _).mpr hnu
            have h2 : w ∈ IsLocalRing.maximalIdeal ↥A := by
              have this := Ideal.sub_mem _ htm h1
              rw [sub_sub_cancel] at this
              refine this
            refine (IsLocalRing.mem_maximalIdeal _).mp h2 hw
          have hprod : β * (t - w) ∈ I ^ n := by
            have : α - β * w = β * (t - w) := by
              rw [ht]
              ring
            rw [this] at hmem
            refine hmem
          have this := Ideal.mul_mem_right (↑htw.unit⁻¹ : ↥A) _ hprod
          rw [mul_assoc, IsUnit.mul_val_inv, mul_one] at this
          refine this
      refine ⟨1, ?_⟩
      rw [Units.val_one, mul_one, ht, hβ, zero_mul]
  ·
    rename_i hdiv
    obtain ⟨t, ht⟩ := hdiv
    if htu : IsUnit t then
      refine ⟨htu.unit⁻¹, ?_⟩
      rw [ht, mul_assoc, IsUnit.mul_val_inv, mul_one]
    else
      have htm : t ∈ IsLocalRing.maximalIdeal ↥A := (IsLocalRing.mem_maximalIdeal _).mpr htu
      have hα : α = 0 := by
        apply hsep
        intro n
        cases Nat.eq_zero_or_pos n
        ·
          rename_i hz
          rw [hz, pow_zero, Ideal.one_eq_top]
          refine Submodule.mem_top
        ·
          rename_i hn
          obtain ⟨w, hw, hmem⟩ := hred n hn
          have htw : IsUnit (1 - t * w) := by
            by_contra hnu
            have h1 : 1 - t * w ∈ IsLocalRing.maximalIdeal ↥A := (IsLocalRing.mem_maximalIdeal _).mpr hnu
            have h2 : (1 : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
              have this := Ideal.add_mem _ h1 (Ideal.mul_mem_right w _ htm)
              rw [sub_add_cancel] at this
              refine this
            refine (IsLocalRing.maximalIdeal.isMaximal ↥A).ne_top (Ideal.eq_top_of_isUnit_mem _ h2 isUnit_one)
          have hprod : α * (1 - t * w) ∈ I ^ n := by
            have : α - β * w = α * (1 - t * w) := by
              rw [ht]
              ring
            rw [this] at hmem
            refine hmem
          have this := Ideal.mul_mem_right (↑htw.unit⁻¹ : ↥A) _ hprod
          rw [mul_assoc, IsUnit.mul_val_inv, mul_one] at this
          refine this
      refine ⟨1, ?_⟩
      rw [Units.val_one, mul_one, hα]
      rw [ht, hα, zero_mul]


-- created on 2026-10-20
