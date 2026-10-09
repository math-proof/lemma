import Mathlib
import sympy.Basic


/--
[AddSubgroup_factorial_nsmul_mem_of_le_of_natCard_le_mul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AddSubgroup_factorial_nsmul_mem_of_le_of_natCard_le_mul.lean)
-/
@[main]
private lemma main
  [AddCommGroup M]
  {H K : AddSubgroup M} [Finite K]
  {C : ℕ}
-- given
  (hHK : H ≤ K)
  (hC : Nat.card K ≤ Nat.card H * C) :
-- imply
  ∀ g ∈ K, (Nat.factorial C) • g ∈ H := by
-- proof
  intro g hg

  set H' : AddSubgroup K := H.addSubgroupOf K with hH'
  have hcardH' : Nat.card H' = Nat.card H := by
    rw [hH']
    exact Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hHK).toEquiv
  have hpos : 0 < Nat.card H := hcardH' ▸ Nat.card_pos
  have hidx : H'.index * Nat.card H' = Nat.card K := H'.index_mul_card
  have hle : H'.index ≤ C := by
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    rwa [← hcardH', hidx, hcardH', mul_comm C]
  have hne : H'.index ≠ 0 := AddSubgroup.index_ne_zero_of_finite
  obtain ⟨q, hq⟩ : H'.index ∣ Nat.factorial C := Nat.dvd_factorial (Nat.pos_of_ne_zero hne) hle
  have hmem : H'.index • (⟨g, hg⟩ : K) ∈ H' := AddSubgroup.nsmul_index_mem H' ⟨g, hg⟩
  rw [hH', AddSubgroup.mem_addSubgroupOf] at hmem
  have hmem' : H'.index • g ∈ H := by simpa using hmem
  rw [hq]
  have : (H'.index * q) • g = q • (H'.index • g) := by rw [mul_nsmul, smul_comm]
  rw [this]
  exact H.nsmul_mem hmem' q


-- created on 2026-10-09
