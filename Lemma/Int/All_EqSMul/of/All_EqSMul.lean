import Mathlib
import sympy.Basic


/--
[SubtractionMonoid_exists_zsmul_eq_of_forall_prime](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_SubtractionMonoid_exists_zsmul_eq_of_forall_prime.lean)
-/
@[main]
private lemma main
  [SubtractionMonoid A]
-- given
  (h : ∀ p : ℕ, p.Prime → ∀ x : A, ∃ y : A, (p : ℤ) • y = x) :
-- imply
  ∀ n : ℤ, n ≠ 0 → ∀ x : A, ∃ y : A, n • y = x := by
-- proof
  have core : ∀ k : ℕ, k ≠ 0 → ∀ x : A, ∃ y : A, (k : ℤ) • y = x := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk x
      rcases eq_or_ne k 1 with rfl | hk1
      · exact ⟨x, by simp⟩
      · obtain ⟨p, hp, m, rfl⟩ : ∃ p, p.Prime ∧ ∃ m, k = p * m := by
          obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd hk1
          exact ⟨p, hp, hd⟩
        have hm : m ≠ 0 := fun h0 => hk (by simp [h0])
        have hmlt : m < p * m := by nlinarith [hp.one_lt, Nat.pos_of_ne_zero hm]
        obtain ⟨z, hz⟩ := h p hp x
        obtain ⟨y, hy⟩ := ih m hmlt hm z
        exact ⟨y, by rw [Nat.cast_mul, mul_zsmul, hy, hz]⟩
  intro n hn x
  have hna : n.natAbs ≠ 0 := fun h0 => hn (Int.natAbs_eq_zero.mp h0)
  rcases Int.natAbs_eq n with he | he
  · obtain ⟨y, hy⟩ := core n.natAbs hna x
    exact ⟨y, by rw [he]; exact hy⟩
  · obtain ⟨y, hy⟩ := core n.natAbs hna x
    exact ⟨-y, by rw [he, neg_zsmul, zsmul_neg, neg_neg, hy]⟩


-- created on 2026-10-05
