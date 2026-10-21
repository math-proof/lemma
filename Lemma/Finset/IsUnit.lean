import Mathlib
import sympy.Basic
open IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[DrinfeldCurve_LocalChart_isUnit_sum_pow_mul_pow_of_pow_mul_sub_mul_pow_mem_maximalIdeal](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_DrinfeldCurve_LocalChart_isUnit_sum_pow_mul_pow_of_pow_mul_sub_mul_pow_mem_maximalIdeal.lean)
-/
@[path]
private lemma main
  {q : ℕ} [Fact q.Prime]
  {W : Type} [CommRing W] [IsLocalRing W]
  {a b : W}
  -- given
  (hqW : (q : W) ∈ maximalIdeal W)
  (hab : a ∉ maximalIdeal W ∨ b ∉ maximalIdeal W)
  (hdir : a ^ q * b - a * b ^ q ∈ maximalIdeal W) :
  -- imply
  IsUnit (∑ i ∈ Finset.range (q + 1), a ^ ((q - 1) * i) * b ^ ((q - 1) * (q - i))) := by
  -- proof
  classical
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
  have hq1 : 1 ≤ q - 1 := by omega
  set k := ResidueField W
  set π : W →+* k := IsLocalRing.residue W
  have hπmem : ∀ x : W, x ∈ maximalIdeal W ↔ π x = 0 := fun x => (IsLocalRing.residue_eq_zero_iff x).symm
  suffices key : ∀ x : W, π x ≠ 0 → IsUnit x by
    apply key
    rw [map_sum]
    simp only [map_mul, map_pow]
    have hqk : (q : k) = 0 := by
      simpa using Iff.mp (hπmem _) hqW
    have hdir' : π a ^ q * π b = π a * π b ^ q := by
      have := Iff.mp (hπmem _) hdir
      rw [map_sub, sub_eq_zero] at this
      simpa [map_mul, map_pow] using this
    have hab' : π a ≠ 0 ∨ π b ≠ 0 := by
      obtain h | h := hab
      · apply Or.inl fun h0 => h (Iff.mpr (hπmem a) h0)
      · apply Or.inr fun h0 => h (Iff.mpr (hπmem b) h0)
    have hsum : (∑ i ∈ Finset.range (q + 1), π a ^ ((q - 1) * i) * π b ^ ((q - 1) * (q - i))) = ∑ i ∈ Finset.range (q + 1), (π a ^ (q - 1)) ^ i * (π b ^ (q - 1)) ^ (q - i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← pow_mul, ← pow_mul]
    rw [hsum]
    set α := π a ^ (q - 1) with hα
    set β := π b ^ (q - 1) with hβ
    if hA : π a = 0 then
      have hB : π b ≠ 0 := hab'.resolve_left (not_not.mpr hA)
      have hα0 : α = 0 := by
        rw [hα, hA]
        apply zero_pow (by omega)
      rw [Finset.sum_eq_single_of_mem 0 (by simp) (fun j hj hj0 => by rw [hα0, zero_pow hj0, zero_mul])]
      simp only [pow_zero, one_mul, Nat.sub_zero]
      apply pow_ne_zero _ (pow_ne_zero _ hB)
    else
      if hB : π b = 0 then
        have hβ0 : β = 0 := by
          rw [hβ, hB]
          apply zero_pow (by omega)
        rw [Finset.sum_eq_single_of_mem q (by simp) (fun j hj hjq => by
          have hjq' : q - j ≠ 0 := by
            have : j < q + 1 := Iff.mp Finset.mem_range hj
            omega
          rw [hβ0, zero_pow hjq', mul_zero])]
        simp only [Nat.sub_self, pow_zero, mul_one]
        apply pow_ne_zero _ (pow_ne_zero _ hA)
      else
        have hαβ : α = β := by
          have h1 : π a * π b * (α - β) = 0 := by
            have e1 : π a ^ q = π a * α := by
              rw [hα, ← pow_succ']
              congr 1
              omega
            have e2 : π b ^ q = π b * β := by
              rw [hβ, ← pow_succ']
              congr 1
              omega
            have := hdir'
            rw [e1, e2] at this
            linear_combination this
          obtain h2 | h2 := Iff.mp mul_eq_zero h1
          ·
            obtain h3 | h3 := Iff.mp mul_eq_zero h2
            · apply absurd h3 hA
            · apply absurd h3 hB
          · apply Iff.mp sub_eq_zero h2
        have hterm : ∀ i ∈ Finset.range (q + 1), α ^ i * β ^ (q - i) = α ^ q := by
          intro i hi
          have : i ≤ q := Iff.mp Nat.lt_succ_iff (Iff.mp Finset.mem_range hi)
          rw [← hαβ, ← pow_add]
          congr 1
          omega
        rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have : ((q + 1 : ℕ) : k) = 1 := by
          push_cast
          rw [hqk, zero_add]
        rw [this, one_mul]
        apply pow_ne_zero
        rw [hα]
        apply pow_ne_zero _ hA
  intro x hx
  by_contra h
  apply hx (Iff.mp (hπmem x) (Iff.mpr (IsLocalRing.mem_maximalIdeal x) h))


-- created on 2026-10-20
