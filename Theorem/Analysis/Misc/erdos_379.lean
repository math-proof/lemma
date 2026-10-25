import Mathlib
open Nat

/-! Formalizing a proof of Erdos problem \#379, arising from conversations between Stijn Cambie, Vjeko Kovac, and Terry Tao.  See the discussion at https://www.erdosproblems.com/forum/thread/379 -/


/-- $$`\binom\{n\}\{k\} \cdot k = \binom\{n-1\}\{k-1\} \cdot n`. -/
theorem binom_eq {n k:ℕ} (hk: 1 ≤ k) : (n.choose k) * k = ((n-1).choose (k-1)) * n := by
  rcases le_or_gt k n with _ | hn
  . symm; rw [←choose_symm]; nth_rewrite 2 [←choose_symm]
    convert choose_mul_succ_eq ?_ ((n-1)-(k-1)) using 3
    all_goals omega
  simp [choose_eq_zero_of_lt hn, choose_eq_zero_iff]; omega

/-- $$`\binom\{n\}\{k\} \cdot k \cdot (k-1) = \binom\{n-2\}\{k-2\} \cdot (n-1) \cdot n`. -/
theorem binom_eq_2 {n k:ℕ} (hk: 2 ≤ k) : (n.choose k) * k * (k-1) = ((n-2).choose (k-2)) * (n-1) * n := calc
  _ = ((n-1).choose (k-1)) * n * (k-1) := by rw [binom_eq]; omega
  _ = ((n-1).choose (k-1)) * (k-1) * n := by ring
  _ = _ := by
    rw [binom_eq]; congr 2
    all_goals omega

/-- If $$`p^\{a+b+1\} \mid n$$, then $$p^\{a+1\} \mid \binom\{n\}\{k\}$$ or $$p^\{b+1\} \mid k`. -/
theorem lemma_1 {n k p a b:ℕ} (hk: 1 ≤ k)
 (hp: p.Prime) (h1: p^(a+b+1) ∣ n) : p^(a+1) ∣ n.choose k ∨ p^(b+1) ∣ k := by
  replace h1 := h1.trans (dvd_mul_left _ ((n-1).choose (k-1)))
  rw [←binom_eq hk] at h1; contrapose! h1; apply finiteMultiplicity_mul_aux hp.prime <;> tauto

/-- If $$`p^r \mid n-1$$ and $$k,n-k$$ are not divisible by $$p$$, then $$p^r \mid \binom\{n\}\{k\}`. -/
theorem lemma_2 {n k p r:ℕ} (hk: 2 ≤ k) (hn: k ≤ n)
 (hp: p.Prime) (h1: p^r ∣ n-1) (hr: 0 < r) (h2: ¬p∣k) (h3: ¬ p∣n-k) : p^r ∣ n.choose k := by
  have h1' : p ∣ n-1 := (dvd_pow_self _ (by omega)).trans h1
  replace h1 := (h1.trans (dvd_mul_left _ ((n-2).choose (k-2)))).trans (dvd_mul_right _ n)
  rw [←binom_eq_2 hk] at h1
  replace h3 : ¬p∣k-1 := by contrapose! h3; convert dvd_sub h1' h3 using 1; omega
  exact hp.prime.pow_dvd_of_dvd_mul_right _ h2 (hp.prime.pow_dvd_of_dvd_mul_right _ h3 h1)

/-- If $$`n=2^\{\phi(p^R)\}$$ and $$p>2^\{r-1\}$$, then $$2^r \mid \binom\{n\}\{k\}$$ or $$p^R \mid \binom\{n\}\{k\}`. -/
theorem key_prop {k n p r R:ℕ} (hn: n = 2^((p^R).totient))
  (hk: 1 ≤ k) (hkn: k < n) (hp: p.Prime) (hpr: p > 2^(r-1))
  (hr: 1 < r) (hr' : r ≤ (p^R).totient):
  2^r ∣ n.choose k ∨ p^R ∣ n.choose k := by
  set m := (p^R).totient
  have : 2 ^ (r - 1 + 1) ∣ n.choose k ∨ 2 ^ (m - r + 1) ∣ k := by
    convert lemma_1 hk ?_ dvd_rfl; rw [hn]; congr; omega; decide
  rcases this with this | this
  . left; convert this; omega
  have hcoprime : Coprime 2 p := by simp; apply hp.odd_of_ne_two; grind [Nat.le_self_pow]
  have hrm : n = 2^(r-1) * 2^(m-r+1) := by rw [hn,←pow_add]; congr; omega
  have _ : 2^(r-1) * 2^(m-r+1) < p * 2^(m-r+1) := by gcongr
  right; apply lemma_2 _ (by order) hp
  . rw [←modEq_iff_dvd',hn]; symm; apply_rules [ModEq.pow_totient, Coprime.pow_right]; omega
  . by_contra!; simp_all [m]; omega
  . by_contra! h
    apply (hcoprime.symm.pow_right _).mul_dvd_of_dvd_of_dvd h at this
    apply le_of_dvd at this <;> grind
  . by_contra! h
    have : 2^(m-r+1) ∣ n-k := by rw [hrm]; apply_rules [dvd_sub, dvd_mul_left]
    apply (hcoprime.symm.pow_right _).mul_dvd_of_dvd_of_dvd h at this
    apply le_of_dvd at this <;> omega
  apply (Nat.le_self_pow _ _).trans (le_of_dvd _ this) <;> omega

