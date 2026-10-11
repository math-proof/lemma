import sympy.Basic
import Mathlib.Data.Nat.Log


@[path]
private lemma main
  [CommSemiring α]
  {n : ℕ}
  {x : Fin n → α}
  {c p : Fin (2 ^ n) → α}
-- given
  (hp0 : p 0 = 1)
  (hp : ∀ k : Fin (2 ^ n), (hk : (k : ℕ) ≠ 0) →
    p k = x ⟨Nat.log2 (k : ℕ), by
      rw [Nat.log2_eq_log_two]
      exact Nat.log_lt_of_lt_pow hk k.isLt⟩ *
      p ⟨(k : ℕ) - 2 ^ Nat.log2 (k : ℕ), by
        have h1 := k.isLt
        have h2 := Nat.sub_le (k : ℕ) (2 ^ Nat.log2 (k : ℕ))
        omega⟩) :
-- imply
  p ⬝ᵥ c = ∑ k, c k * ∏ i, x i ^ ((k : ℕ) / 2 ^ (i : ℕ) % 2) := by
-- proof
  have key : ∀ q : ℕ, ∀ hf : q < 2 ^ n, p ⟨q, hf⟩ = ∏ i, x i ^ (q / 2 ^ (i : ℕ) % 2) := by
    intro q
    induction q using Nat.strong_induction_on with
    | _ q ih =>
      intro hf
      if h0 : q = 0 then
        subst h0
        show p 0 = ∏ i, x i ^ ((0 : ℕ) / 2 ^ (i : ℕ) % 2)
        rw [hp0]
        simp
      else
        have hm0 : 0 < q := Nat.pos_of_ne_zero h0
        have hjn : Nat.log2 q < n := by
          rw [Nat.log2_eq_log_two]
          exact Nat.log_lt_of_lt_pow h0 hf
        have hlow : 2 ^ Nat.log2 q ≤ q :=
          Nat.pow_le_of_le_log (b := 2) (y := q) h0 (by rw [Nat.log2_eq_log_two])
        have hhigh : q < 2 * 2 ^ Nat.log2 q := by
          have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) q
          rw [← Nat.log2_eq_log_two] at h
          have h2 : 2 ^ (Nat.log2 q).succ = 2 * 2 ^ Nat.log2 q := by
            rw [Nat.succ_eq_add_one, Nat.pow_succ, Nat.mul_comm]
          omega
        have hpk := hp ⟨q, hf⟩ h0
        have hpos : 0 < 2 ^ Nat.log2 q := by positivity
        rw [hpk, ih (q - 2 ^ Nat.log2 q) (by omega) (by omega)]
        have hq : q / 2 ^ Nat.log2 q = 1 := by
          have h1 : 0 < q / 2 ^ Nat.log2 q := Nat.div_pos hlow (by positivity)
          have h2 : q / 2 ^ Nat.log2 q < 2 := by
            rw [Nat.div_lt_iff_lt_mul (by positivity)]
            omega
          omega
        have hbj1 : q / 2 ^ Nat.log2 q % 2 = 1 := by rw [hq]
        have hbj0 : (q - 2 ^ Nat.log2 q) / 2 ^ Nat.log2 q % 2 = 0 := by
          rw [Nat.div_eq_of_lt (by omega), Nat.zero_mod]
        have hparity : ∀ i : ℕ, i < Nat.log2 q →
            q / 2 ^ i % 2 = (q - 2 ^ Nat.log2 q) / 2 ^ i % 2 := by
          intro i hi
          have hpow : 2 ^ Nat.log2 q = 2 ^ i * 2 ^ (Nat.log2 q - i) := by
            rw [← Nat.pow_add]
            congr 1
            omega
          have hme : q = (q - 2 ^ Nat.log2 q) + 2 ^ Nat.log2 q := by omega
          have hdiv : q / 2 ^ i = (q - 2 ^ Nat.log2 q) / 2 ^ i + 2 ^ (Nat.log2 q - i) := by
            conv_lhs =>
              rw [hme, hpow]
            rw [Nat.add_mul_div_left _ _ (by positivity), ← hpow]
          have hj1 : Nat.log2 q - i = (Nat.log2 q - i - 1) + 1 := by omega
          rw [hdiv, hj1, Nat.pow_succ, Nat.mul_comm (2 ^ (Nat.log2 q - i - 1)) 2,
            Nat.add_mul_mod_self_left]
        have hsplit : ∀ i : Fin n, (i : ℕ) ≠ Nat.log2 q →
            q / 2 ^ (i : ℕ) % 2 = (q - 2 ^ Nat.log2 q) / 2 ^ (i : ℕ) % 2 := by
          intro i hi
          obtain hlt | hgt := Nat.lt_or_gt_of_ne hi
          · exact hparity (i : ℕ) hlt
          ·
            have hli : Nat.log 2 q < (i : ℕ) := by
              rw [← Nat.log2_eq_log_two]
              omega
            have hlt1 : q < 2 ^ (i : ℕ) :=
              (Nat.log_lt_iff_lt_pow (b := 2) (by norm_num) h0).mp hli
            have hlt2 : q - 2 ^ Nat.log2 q < 2 ^ (i : ℕ) := by omega
            rw [Nat.div_eq_of_lt hlt1, Nat.div_eq_of_lt hlt2]
        have hje : (⟨Nat.log2 q, hjn⟩ : Fin n) ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
        rw [← Finset.mul_prod_erase Finset.univ
            (fun i : Fin n => x i ^ ((q - 2 ^ Nat.log2 q) / 2 ^ (i : ℕ) % 2)) hje,
          hbj0, pow_zero, one_mul,
          ← Finset.mul_prod_erase Finset.univ (fun i : Fin n => x i ^ (q / 2 ^ (i : ℕ) % 2)) hje,
          hbj1, pow_one]
        congr 1
        refine Finset.prod_congr rfl fun i hi => ?_
        obtain ⟨hne, -⟩ := Finset.mem_erase.mp hi
        rw [hsplit i (Fin.val_ne_of_ne hne)]
  have keyf : ∀ k : Fin (2 ^ n), p k = ∏ i, x i ^ ((k : ℕ) / 2 ^ (i : ℕ) % 2) :=
    fun k => key (k : ℕ) k.isLt
  show ∑ k, p k * c k = ∑ k, c k * ∏ i, x i ^ ((k : ℕ) / 2 ^ (i : ℕ) % 2)
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [keyf k, mul_comm (∏ i, x i ^ ((k : ℕ) / 2 ^ (i : ℕ) % 2)) (c k)]


-- created on 2021-12-23
