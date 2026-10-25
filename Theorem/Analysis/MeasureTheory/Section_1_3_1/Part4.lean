import Theorem.Analysis.MeasureTheory.Section_1_2_3.Part2
import Theorem.Analysis.Misc.NatBitwise
import Def.Analysis.MeasureTheory.Section_1_3_1.Part4


namespace UnsignedSimpleFunction.IntegralWellDef

open scoped Classical

/-- Atoms are pairwise disjoint -/
lemma atom_pairwiseDisjoint {X : Type*} {k k' : ℕ} (E : Fin k → Set X) (E' : Fin k' → Set X) :
    Set.univ.PairwiseDisjoint (atom E E') := by
  intro i _ j _ hij
  simp only [Function.onFun]
  rw [Set.disjoint_left]
  intro x hxi hxj
  simp only [atom, Set.mem_setOf_eq, atomMembership_eq_testBit] at hxi hxj
  -- If i ≠ j, they differ in some bit
  have hne : i.val ≠ j.val := Fin.val_ne_of_ne hij
  obtain ⟨bit, hbit⟩ := Nat.exists_testBit_ne_of_ne hne
  -- The bit must be < k + k' since both i, j < 2^(k+k')
  have hi_lt : i.val < 2^(k + k') := i.isLt
  have hj_lt : j.val < 2^(k + k') := j.isLt
  have hbit_bound : bit < k + k' := by
    by_contra h
    push_neg at h
    have hi_false : i.val.testBit bit = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hi_lt (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) h))
    have hj_false : j.val.testBit bit = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hj_lt (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) h))
    exact hbit (hi_false.trans hj_false.symm)
  -- Now we know bit < k + k', so it indexes into E or E'
  by_cases hbit_k : bit < k
  · -- bit indexes into E
    have hi_iff := hxi.1 ⟨bit, hbit_k⟩
    have hj_iff := hxj.1 ⟨bit, hbit_k⟩
    -- hxi and hxj both give x ∈ E ⟨bit, _⟩ ↔ testBit = true
    -- But i and j have different bits, so one says x ∈ E and the other says x ∉ E
    cases h_i : i.val.testBit bit <;> cases h_j : j.val.testBit bit
    · exact hbit (h_i.trans h_j.symm)
    · have hx_in : x ∈ E ⟨bit, hbit_k⟩ := hj_iff.mp h_j
      have hx_out : x ∉ E ⟨bit, hbit_k⟩ := fun h => by simp [hi_iff.mpr h] at h_i
      exact hx_out hx_in
    · have hx_in : x ∈ E ⟨bit, hbit_k⟩ := hi_iff.mp h_i
      have hx_out : x ∉ E ⟨bit, hbit_k⟩ := fun h => by simp [hj_iff.mpr h] at h_j
      exact hx_out hx_in
    · exact hbit (h_i.trans h_j.symm)
  · -- bit indexes into E' (bit ∈ [k, k+k'))
    have hbit_k' : bit - k < k' := by omega
    have h_add : k + (bit - k) = bit := by omega
    have hi_iff := hxi.2 ⟨bit - k, hbit_k'⟩
    have hj_iff := hxj.2 ⟨bit - k, hbit_k'⟩
    simp only [h_add] at hi_iff hj_iff
    cases h_i : i.val.testBit bit <;> cases h_j : j.val.testBit bit
    · exact hbit (h_i.trans h_j.symm)
    · have hx_in : x ∈ E' ⟨bit - k, hbit_k'⟩ := hj_iff.mp h_j
      have hx_out : x ∉ E' ⟨bit - k, hbit_k'⟩ := fun h => by simp [hi_iff.mpr h] at h_i
      exact hx_out hx_in
    · have hx_in : x ∈ E' ⟨bit - k, hbit_k'⟩ := hi_iff.mp h_i
      have hx_out : x ∉ E' ⟨bit - k, hbit_k'⟩ := fun h => by simp [hj_iff.mpr h] at h_j
      exact hx_out hx_in
    · exact hbit (h_i.trans h_j.symm)

/-- Sum of powers of 2 up to n equals 2^n - 1 -/
private lemma sum_pow_two_range (n : ℕ) : ∑ i ∈ Finset.range n, (2:ℕ)^i = 2^n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    have h : 1 ≤ 2^n := Nat.one_le_two_pow
    omega

/-- For any subset of {lean}`Fin k`, sum of {given -show (type := "Fin k")}`j` {lean}`2^j.val` is less than {lean}`2^k` -/
private lemma sum_pow_two_fin_lt {k : ℕ} {s : Finset (Fin k)} :
    s.sum (fun j => (2:ℕ)^j.val) < 2^k := by
  have h1 : s.sum (fun j => (2:ℕ)^j.val) ≤ Finset.univ.sum (fun j : Fin k => (2:ℕ)^j.val) := by
    apply Finset.sum_le_sum_of_subset
    exact Finset.subset_univ s
  have h2 : Finset.univ.sum (fun j : Fin k => (2:ℕ)^j.val) = ∑ i ∈ Finset.range k, 2^i := by
    rw [Fin.sum_univ_eq_sum_range]
  have h3 : ∑ i ∈ Finset.range k, (2:ℕ)^i = 2^k - 1 := sum_pow_two_range k
  have h4 : 2^k - 1 < 2^k := Nat.sub_lt Nat.one_le_two_pow Nat.one_pos
  omega

end UnsignedSimpleFunction.IntegralWellDef
