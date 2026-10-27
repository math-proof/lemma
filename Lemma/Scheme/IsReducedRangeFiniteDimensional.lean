import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[IsReduced_range_of_finiteDimensional](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsReduced_range_of_finiteDimensional.lean)
-/
@[path]
private lemma main
  [Field K] [CommRing A] [Algebra K A] [FiniteDimensional K A] [IsReduced A] [Ring B] [Algebra K B]
  (f : AlgHom K A B) :
  -- imply
  IsReduced ↥f.range := by
  -- proof
  let _ : IsArtinianRing A := IsArtinianRing.of_finite K A
  have vnr : ∀ a : A, ∃ z : A, a = a * a * z := by
    intro a
    obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd a (1 : A)
    simp only [smul_eq_mul, mul_one] at hy
    simp only [Nat.succ_eq_add_one] at hy
    cases n with
    | zero =>
      refine ⟨y, ?_⟩
      rw [zero_add, pow_one, pow_zero] at hy
      rw [mul_assoc, hy, mul_one]
    | succ m =>
      set u : A := a ^ (m + 1) * y ^ (m + 1) with hu
      have hpow : ∀ k : ℕ, a ^ (m + 1) = a ^ (m + 1) * (a * y) ^ k := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          calc
            _ = a ^ (m + 1) * (a * y) ^ k := ih
            _ = (a ^ (m + 1 + 1) * y) * (a * y) ^ k := by
              rw [hy]
            _ = a ^ (m + 1) * (a * y) ^ (k + 1) := by
              ring
      have hu' : a ^ (m + 1) * (1 - u) = 0 := by
        rw [hu, mul_sub, mul_one, ← mul_pow, ← hpow (m + 1), sub_self]
      have hb : IsNilpotent (a - a * a * (a ^ m * y ^ (m + 1))) := by
        refine ⟨m + 1, ?_⟩
        have : a - a * a * (a ^ m * y ^ (m + 1)) = a * (1 - u) := by
          rw [hu]
          ring
        rw [this, mul_pow, pow_succ' (1 - u), ← mul_assoc, hu', zero_mul]
      refine ⟨a ^ m * y ^ (m + 1), sub_eq_zero.mp hb.eq_zero⟩
  rw [isReduced_iff]
  rintro ⟨x, hx⟩ hnil
  obtain ⟨a, rfl⟩ := f.mem_range.mp hx
  obtain ⟨z, hz⟩ := vnr a
  have hk : ∀ k : ℕ, a = a ^ (k + 1) * z ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        _ = a * a * z := hz
        _ = a * (a ^ (k + 1) * z ^ k) * z := by
          rw [← ih]
        _ = a ^ (k + 1 + 1) * z ^ (k + 1) := by
          ring
  obtain ⟨m, hm⟩ := hnil
  have hm' : (f a) ^ m = 0 := by
    have := congrArg Subtype.val hm
    simpa using this
  refine Subtype.ext ?_
  show f a = 0
  cases m with
  | zero =>
    rw [pow_zero] at hm'
    let _ := subsingleton_of_zero_eq_one hm'.symm
    apply Subsingleton.elim _ _
  | succ m =>
    rw [hk m, map_mul, map_pow, map_pow, hm', zero_mul]


-- created on 2026-10-20
