import Mathlib
import sympy.Basic


/--
[AddSubgroup_exists_units_zmod_val_smul_eq_of_addOrderOf_eq_of_mem_zmultiples](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AddSubgroup_exists_units_zmod_val_smul_eq_of_addOrderOf_eq_of_mem_zmultiples.lean)
-/
@[path]
private lemma main
  [AddCommGroup G]
  {ℓ : ℕ} [NeZero ℓ]
  {P P' : G}
-- given
  (hP : addOrderOf P = ℓ)
  (hP' : addOrderOf P' = ℓ)
  (h : P' ∈ AddSubgroup.zmultiples P) :
-- imply
  ∃ d : (ZMod ℓ)ˣ, P' = (d : ZMod ℓ).val • P := by
-- proof
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp h
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne ℓ

  set n : ℕ := (k % ℓ).toNat with hn
  have hkn : k • P = n • P := by
    have hℓP : (ℓ : ℤ) • P = 0 := by
      rw [natCast_zsmul, ← hP]; exact addOrderOf_nsmul_eq_zero P
    have hnn : 0 ≤ k % ℓ := Int.emod_nonneg k hℓ0
    calc k • P = (ℓ * (k / ℓ) + k % ℓ) • P := by rw [Int.mul_ediv_add_emod]
      _ = (k / ℓ) • ((ℓ : ℤ) • P) + (k % ℓ) • P := by rw [add_zsmul, mul_comm, mul_zsmul]
      _ = (k % ℓ) • P := by rw [hℓP, zsmul_zero, zero_add]
      _ = n • P := by rw [hn, ← natCast_zsmul, Int.toNat_of_nonneg hnn]
  have hnlt : n < ℓ := by
    have := Int.emod_lt_of_pos k (Int.natCast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne ℓ)))
    omega

  have hcop : n.Coprime ℓ := by
    by_cases hn0 : n = 0
    ·
      rw [hkn, hn0, zero_smul, addOrderOf_zero] at hP'
      rw [hn0, ← hP']; exact Nat.coprime_one_right 0
    · have h1 := addOrderOf_nsmul' P hn0
      rw [← hkn, hP', hP] at h1
      have : Nat.gcd ℓ n = 1 := by
        rcases Nat.div_eq_self.mp h1.symm with h | h
        · exact absurd h (NeZero.ne ℓ)
        · exact h
      rw [Nat.coprime_comm]; exact this
  refine ⟨ZMod.unitOfCoprime n hcop, ?_⟩
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hnlt, hkn]


-- created on 2026-10-05
