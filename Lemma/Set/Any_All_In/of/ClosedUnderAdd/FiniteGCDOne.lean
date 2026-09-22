import Mathlib.Data.Int.GCD
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Lemma.Set.InMul.of.In.Gt_0
import Lemma.Set.Sum_Mul.of.Nonempty.All_In.Gt_0.In
import Lemma.Finset.Any_EqGcd.of.Nonempty
import sympy.core.intfunc
open Set Finset


@[main]
private lemma main
  {A : Set ℕ} [ClosedUnderAdd A] [FiniteGCDOne A] :
-- imply
  ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → n ∈ A := by
-- proof
  obtain ⟨s, hsa, hgcd1, h0, hs⟩ := (inferInstance : FiniteGCDOne A).finite_gcd_one
  obtain ⟨c, hgcd⟩ := Finset.Any_EqGcd.of.Nonempty hs
  rw [hgcd1] at hgcd
  let m : ℤ := (s.sum id : ℕ)
  have hmpos : 0 < m := by
    unfold m
    simp
    obtain ⟨i, hi⟩ := hs
    have : i ≠ 0 := by
      intro h
      exact h0 (by simpa [h] using hi)
    have : 0 < (i : ℤ) := by
      exact_mod_cast (Nat.pos_of_ne_zero this)
    apply sum_pos'
    · intro x hx; simp
    · exact ⟨i, hi, this⟩
  let c_bound := s.sum fun i => |c i|
  have hcmax : ∀ i ∈ s, |c i| ≤ c_bound := by
    intro i hi; unfold c_bound;
    rw [←sum_erase_add _ _ hi]
    simp
    apply sum_nonneg
    intro j hj; simp [abs_nonneg]
  have hcnonneg : 0 ≤ c_bound := by
    unfold c_bound
    have : (0 : ℤ) = ∑ i ∈ s, 0 := by simp
    conv_lhs => rw [this]
    apply sum_le_sum
    · simp
  let B := m * m * c_bound + m
  have hBnonneg : 0 ≤ B := by
    apply add_nonneg
    · simp [hcnonneg, hmpos]
    · exact hmpos.le
  have h : ∀ n, B ≤ n → n.toNat ∈ A := by
    intro n hn
    have : n = n / m * m + n % m * (1 : ℕ) := by
      simp
      linarith [Int.ediv_mul_add_emod n m]
    set k := n / m
    set r := n % m
    conv_rhs at this =>
      rw [hgcd]
      unfold m
      simp [mul_comm, sum_mul]
      pattern r * ∑ x ∈ s, c x * x
      simp [mul_comm r _, sum_mul]
    conv_rhs at this =>
      rw [←sum_add_distrib]
    let c' : ℕ → ℤ := fun i => k + r * c i
    have hnrep : n = ∑ i ∈ s, i * c' i := by
      rw [this]
      apply sum_congr rfl _
      intro x hx; ring
    have hcpos : ∀ i ∈ s, 0 < c' i := by
      intro i hi
      unfold c'
      have : -(r * c i) ≤ m * c_bound := by calc
          -(r * c i)
        _ ≤ |r * c i| := neg_le_abs (r * c i)
        _ = |r| * |c i| := abs_mul r (c i)
        _ ≤ |r| * c_bound := by
          have := hcmax i hi
          gcongr
        _ ≤ r * c_bound := by
          have : 0 ≤ r := by
            have := Int.emod_nonneg n hmpos.ne'
            exact this
          simp [abs_of_nonneg this]
        _ ≤ m * c_bound := by
          have := Int.emod_lt n hmpos.ne'
          rw [Int.natAbs_of_nonneg hmpos.le] at this
          gcongr
      have : m * c_bound < k := by
        unfold k
        unfold B at hn
        have := Int.ediv_le_ediv hmpos hn
        have hcancel : (m * m * c_bound + m * 1) / m
          = m * c_bound + 1 := by
          simp only [mul_assoc, ←mul_add]
          simp [mul_comm _ (m * c_bound + 1)]
          apply Int.mul_ediv_cancel
          · exact hmpos.ne'
        simp at hcancel
        rw [hcancel] at this
        linarith
      linarith
    simp [hnrep]
    have hnonneg : ∀ i ∈ s, 0 ≤ i * c' i := by
      intro i hi
      apply mul_nonneg
      · simp
      · exact le_of_lt (hcpos i hi)
    have hsum_toNat : (∑ i ∈ s, (↑i : ℤ) * c' i).toNat = ∑ i ∈ s, ((↑i : ℤ) * c' i).toNat := by
      apply Int.natCast_inj.mp
      rw [Int.toNat_of_nonneg (sum_nonneg hnonneg)]
      symm
      rw [Nat.cast_sum]
      apply sum_congr rfl
      intro i hi
      rw [Int.toNat_of_nonneg (hnonneg i hi)]
    rw [hsum_toNat]
    have htoNat_mul : ∀ i ∈ s, ((↑i : ℤ) * c' i).toNat = i * (c' i).toNat := by
      intro i hi
      have ha : 0 ≤ (i : ℤ) := by simp
      have hb : 0 ≤ c' i := le_of_lt (hcpos i hi)
      apply Int.natCast_inj.mp
      rw [Int.toNat_of_nonneg (mul_nonneg ha hb), Nat.cast_mul, Int.toNat_of_nonneg hb]
    rw [sum_congr rfl htoNat_mul]
    apply Set.Sum_Mul.of.Nonempty.All_In.Gt_0.In (hs := hs)
    · intro i hi; simp; exact ⟨hsa hi, hcpos i hi⟩
  refine ⟨?n₀, ?hn₀⟩
  case n₀ => exact B.toNat
  case hn₀ =>
    intro n hn
    have := h n (Int.toNat_le.mp hn)
    simp at this
    exact this


-- created on 2026-09-18
