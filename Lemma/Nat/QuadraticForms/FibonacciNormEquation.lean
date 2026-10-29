import Mathlib
import Initialize.Tactic.Attr.Basic


namespace FibonacciNormEquation

/--
[fib_add_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/FibonacciNormEquation.lean)
-/
@[path]
private lemma fib_add_succ (n : ℤ) : Int.fib (n + 1) = Int.fib n + Int.fib (n - 1) := by
  have h := Int.fib_add_two (n - 1)
  have e1 : n - 1 + 2 = n + 1 := by ring
  have e2 : n - 1 + 1 = n := by ring
  rw [e1, e2] at h
  linarith

end FibonacciNormEquation

namespace FibonacciNormEquation

/--
[cassini_norm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/FibonacciNormEquation.lean)
-/
@[path]
private lemma cassini_norm (n : ℤ) :
  Int.fib n ^ 2 - Int.fib n * Int.fib (n - 1) - Int.fib (n - 1) ^ 2 =
    -(-1 : ℤ) ^ n.natAbs := by
  have hF := fib_add_succ n
  have cass := Int.fib_succ_mul_fib_pred_sub_fib_sq n
  rw [hF] at cass
  linear_combination -cass

end FibonacciNormEquation

namespace FibonacciNormEquation

/--
[neg_fib_shift](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/FibonacciNormEquation.lean)
-/
@[path]
private lemma neg_fib_shift (n : ℤ) :
  ∃ m s' : ℤ, (s' = 1 ∨ s' = -1) ∧ Int.fib n = s' * Int.fib m ∧
    -(Int.fib n + Int.fib (n - 1)) = s' * Int.fib (m - 1) := by
  obtain hev | hodd := Int.even_or_odd n
  · refine ⟨-n, -1, Or.inr rfl, ?_, ?_⟩
    · have hFn : Int.fib (-n) = -Int.fib n := by rw [Int.fib_neg, ite_eq_left hev]
      rw [hFn]
      ring
    · have hne : ¬Even (n + 1) := by
        obtain ⟨r, hr⟩ := hev
        rintro ⟨s, hs⟩
        omega
      have hFn1 : Int.fib (-n - 1) = Int.fib (n + 1) := by
        have e : -n - 1 = -(n + 1) := by ring
        rw [e, Int.fib_neg, ite_eq_right hne]
      have hF := fib_add_succ n
      rw [hFn1, hF]
      ring
  · refine ⟨-n, 1, Or.inl rfl, ?_, ?_⟩
    · have hne : ¬Even n := by
        obtain ⟨k, hk⟩ := hodd
        rintro ⟨s, hs⟩
        omega
      have hFn : Int.fib (-n) = Int.fib n := by rw [Int.fib_neg, ite_eq_right hne]
      rw [hFn]
      ring
    · have hev2 : Even (n + 1) := by
        obtain ⟨k, hk⟩ := hodd
        exact ⟨k + 1, by omega⟩
      have hFn1 : Int.fib (-n - 1) = -Int.fib (n + 1) := by
        have e : -n - 1 = -(n + 1) := by ring
        rw [e, Int.fib_neg, ite_eq_left hev2]
      have hF := fib_add_succ n
      rw [hFn1, hF]
      ring

end FibonacciNormEquation

namespace FibonacciNormEquation

/--
[fib_nonneg_key](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/FibonacciNormEquation.lean)
-/
@[path]
private lemma fib_nonneg_key : ∀ m : ℕ, ∀ a b : ℤ, 0 ≤ a → 0 ≤ b → |a| + |b| ≤ (m : ℤ) →
  (a ^ 2 - a * b - b ^ 2 = 1 ∨ a ^ 2 - a * b - b ^ 2 = -1) →
  ∃ n : ℤ, a = Int.fib n ∧ b = Int.fib (n - 1) := by
  intro m
  induction m with
  | zero =>
    intro a b ha hb hbound hN
    have ha0 : a = 0 := by
      have h1 := abs_nonneg a
      have h2 := abs_nonneg b
      have h3 : |a| = 0 := by
        push_cast at hbound
        linarith
      exact abs_eq_zero.mp h3
    have hb0 : b = 0 := by
      have h1 := abs_nonneg a
      have h2 := abs_nonneg b
      have h3 : |b| = 0 := by
        push_cast at hbound
        linarith
      exact abs_eq_zero.mp h3
    subst ha0
    subst hb0
    norm_num at hN
  | succ m IH =>
    intro a b ha hb hbound hN
    push_cast at hbound
    rw [abs_of_nonneg ha, abs_of_nonneg hb] at hbound
    by_cases ha0 : a = 0
    · subst ha0
      have hb2 : b ^ 2 = 1 := by
        have hsq := sq_nonneg b
        have e : (0 : ℤ) ^ 2 - 0 * b - b ^ 2 = -(b ^ 2) := by ring
        rw [e] at hN
        obtain h | h := hN <;> linarith
      obtain rfl | rfl := sq_eq_one_iff.mp hb2
      · exact ⟨0, Int.fib_zero.symm, by
        have e : (0 : ℤ) - 1 = -1 := by ring
        rw [e]
        exact Int.fib_neg_one.symm⟩
      · omega
    · by_cases hb0 : b = 0
      · subst hb0
        have ha2 : a ^ 2 = 1 := by
          have hsq := sq_nonneg a
          have e : a ^ 2 - a * (0 : ℤ) - (0 : ℤ) ^ 2 = a ^ 2 := by ring
          rw [e] at hN
          obtain h | h := hN <;> linarith
        obtain rfl | rfl := sq_eq_one_iff.mp ha2
        · exact ⟨1, Int.fib_one.symm, by
          have e : (1 : ℤ) - 1 = 0 := by ring
          rw [e]
          exact Int.fib_zero.symm⟩
        · omega
      · have ha_pos : 0 < a := by omega
        have hb_pos : 0 < b := by omega
        by_cases hle : b ≤ a
        · have e : b ^ 2 - b * (a - b) - (a - b) ^ 2 = -(a ^ 2 - a * b - b ^ 2) := by
            ring_nf
          have hN' : b ^ 2 - b * (a - b) - (a - b) ^ 2 = 1 ∨
            b ^ 2 - b * (a - b) - (a - b) ^ 2 = -1 := by
            obtain h | h := hN
            · exact Or.inr (by linarith)
            · exact Or.inl (by linarith)
          have hbb : |b| + |a - b| ≤ (m : ℤ) := by
            rw [abs_of_nonneg hb, abs_of_nonneg (by omega : 0 ≤ a - b)]
            omega
          obtain ⟨n, hn1, hn2⟩ := IH b (a - b) hb (by omega) hbb hN'
          have hF := fib_add_succ n
          refine ⟨n + 1, ?_, ?_⟩
          · rw [hF]
            linear_combination hn2 + hn1
          · have e2 : n + 1 - 1 = n := by omega
            rw [e2]
            exact hn1
        · push Not at hle
          obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by ring⟩
          have hd : 1 ≤ d := by omega
          have e : a ^ 2 - a * (a + d) - (a + d) ^ 2 = -(a ^ 2) - 3 * (a * d) - d ^ 2 := by
            ring
          have ha2 : 1 ≤ a ^ 2 := by nlinarith [sq_nonneg (a - 1), ha_pos]
          have hd2 : 1 ≤ d ^ 2 := by nlinarith [sq_nonneg (d - 1), hd]
          have had : 1 ≤ a * d := by
            have h1 : (0 : ℤ) ≤ (a - 1) * (d - 1) := mul_nonneg (by omega) (by omega)
            nlinarith [h1, ha_pos, hd]
          have h5 : a ^ 2 - a * (a + d) - (a + d) ^ 2 ≤ -5 := by
            linarith [e, ha2, had, hd2]
          obtain h | h := hN <;> omega

end FibonacciNormEquation

namespace FibonacciNormEquation

/--
[sign_reduce](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/FibonacciNormEquation.lean)
-/
@[path]
private lemma sign_reduce (x y : ℤ)
  (hN : x ^ 2 - x * y - y ^ 2 = 1 ∨ x ^ 2 - x * y - y ^ 2 = -1) :
  ∃ a b : ℤ, 0 ≤ a ∧ 0 ≤ b ∧ (a ^ 2 - a * b - b ^ 2 = 1 ∨ a ^ 2 - a * b - b ^ 2 = -1) ∧
    ((x = a ∧ y = b) ∨ (x = -a ∧ y = -b) ∨ (x = a ∧ y = -a - b) ∨
      (x = -a ∧ y = a + b)) := by
  have step : ∀ u v : ℤ, 0 ≤ u → (u ^ 2 - u * v - v ^ 2 = 1 ∨ u ^ 2 - u * v - v ^ 2 = -1) →
    ∃ a b : ℤ, 0 ≤ a ∧ 0 ≤ b ∧ (a ^ 2 - a * b - b ^ 2 = 1 ∨ a ^ 2 - a * b - b ^ 2 = -1) ∧
      ((u = a ∧ v = b) ∨ (u = a ∧ v = -a - b)) := by
    intro u v hu hN
    by_cases hv : 0 ≤ v
    · exact ⟨u, v, hu, hv, hN, Or.inl ⟨rfl, rfl⟩⟩
    · have hv' : v < 0 := lt_of_not_ge hv
      have e : u ^ 2 - u * (-u - v) - (-u - v) ^ 2 = u ^ 2 - u * v - v ^ 2 := by ring
      have hN' : u ^ 2 - u * (-u - v) - (-u - v) ^ 2 = 1 ∨
        u ^ 2 - u * (-u - v) - (-u - v) ^ 2 = -1 := by
        rwa [e]
      have hb : 0 ≤ -u - v := by
        by_cases hu0 : u = 0
        · subst hu0
          simp only [neg_zero, zero_sub]
          omega
        · have hu1 : 1 ≤ u := by omega
          have hc : u ^ 2 - u * v - v ^ 2 ≤ 1 := by
            obtain h | h := hN <;> linarith
          have hx2 : 1 ≤ u ^ 2 := by nlinarith [sq_nonneg (u - 1), hu1]
          have hprod : v * (-u - v) = (u ^ 2 - u * v - v ^ 2) - u ^ 2 := by ring
          have hle : v * (-u - v) ≤ 0 := by linarith [hprod, hc, hx2]
          by_contra hcon
          push Not at hcon
          have hpos := mul_pos_of_neg_of_neg hv' hcon
          linarith
      exact ⟨u, -u - v, hu, hb, hN', Or.inr ⟨rfl, by ring⟩⟩
  by_cases hx : 0 ≤ x
  · obtain ⟨a, b, ha, hb, hNab, r⟩ := step x y hx hN
    refine ⟨a, b, ha, hb, hNab, ?_⟩
    obtain h | h := r
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
  · have hx' : 0 ≤ -x := by omega
    have eN : (-x) ^ 2 - (-x) * (-y) - (-y) ^ 2 = x ^ 2 - x * y - y ^ 2 := by ring
    have hN' : (-x) ^ 2 - (-x) * (-y) - (-y) ^ 2 = 1 ∨
      (-x) ^ 2 - (-x) * (-y) - (-y) ^ 2 = -1 := by
      rwa [eN]
    obtain ⟨a, b, ha, hb, hNab, r⟩ := step (-x) (-y) hx' hN'
    refine ⟨a, b, ha, hb, hNab, ?_⟩
    obtain ⟨e1, e2⟩ | ⟨e1, e2⟩ := r
    · exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith⟩))

end FibonacciNormEquation

namespace FibonacciNormEquation

/--
[fibonacci_norm_eq_one_or_neg_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/FibonacciNormEquation.lean)
-/
@[path]
lemma fibonacci_norm_eq_one_or_neg_one_iff
  {x y : ℤ} :
-- imply
  (x ^ 2 - x * y - y ^ 2 = 1 ∨ x ^ 2 - x * y - y ^ 2 = -1) ↔
    ∃ n s : ℤ, (s = 1 ∨ s = -1) ∧ x = s * Int.fib n ∧ y = s * Int.fib (n - 1) := by
-- proof
  constructor
  · intro hN
    obtain ⟨a, b, ha, hb, hNab, hrel⟩ := sign_reduce x y hN
    have hble : |a| + |b| ≤ ((a.natAbs + b.natAbs + 1 : ℕ) : ℤ) := by
      have e1 := Int.natCast_natAbs a
      have e2 := Int.natCast_natAbs b
      omega
    obtain ⟨n, hn1, hn2⟩ := fib_nonneg_key (a.natAbs + b.natAbs + 1) a b ha hb hble hNab
    have hF := fib_add_succ n
    obtain ⟨m, s', hs', hm1, hm2⟩ := neg_fib_shift n
    obtain ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ := hrel
    · subst e1
      subst e2
      exact ⟨n, 1, Or.inl rfl, by rw [hn1, one_mul], by rw [hn2, one_mul]⟩
    · subst e1
      subst e2
      exact ⟨n, -1, Or.inr rfl, by rw [hn1]; ring, by rw [hn2]; ring⟩
    · subst e1
      subst e2
      refine ⟨m, s', hs', ?_, ?_⟩
      · rw [hn1]
        exact hm1
      · rw [hn1, hn2]
        linear_combination hm2
    · subst e1
      subst e2
      refine ⟨m, -s', ?_, ?_, ?_⟩
      · rcases hs' with rfl | rfl
        · exact Or.inr rfl
        · exact Or.inl (by norm_num)
      · rw [hn1]
        linear_combination -hm1
      · rw [hn1, hn2]
        linear_combination -hm2
  · intro h
    obtain ⟨n, s, hs, rfl, rfl⟩ := h
    have hs2 : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
    have hE := cassini_norm n
    have hfac : (s * Int.fib n) ^ 2 - (s * Int.fib n) * (s * Int.fib (n - 1)) -
      (s * Int.fib (n - 1)) ^ 2 =
      Int.fib n ^ 2 - Int.fib n * Int.fib (n - 1) - Int.fib (n - 1) ^ 2 := by
      have hss : (s * Int.fib n) ^ 2 - (s * Int.fib n) * (s * Int.fib (n - 1)) -
        (s * Int.fib (n - 1)) ^ 2 =
        s ^ 2 * (Int.fib n ^ 2 - Int.fib n * Int.fib (n - 1) - Int.fib (n - 1) ^ 2) := by
        ring
      rw [hss, hs2, one_mul]
    rw [hfac, hE]
    obtain hC | hC := neg_one_pow_eq_or ℤ n.natAbs
    · rw [hC]
      exact Or.inr (by norm_num)
    · rw [hC]
      exact Or.inl (by norm_num)

end FibonacciNormEquation


-- created on 2026-10-20
-- updated on 2026-10-26
