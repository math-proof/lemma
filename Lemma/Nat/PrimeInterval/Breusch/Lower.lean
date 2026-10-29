import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.PrimeInterval.Breusch.Lower
open MathlibExt MathlibExt.NumberTheory MathlibExt.NumberTheory.BreuschWanted MathlibExt.NumberTheory.BreuschWanted.Internal
open Nat Finset


namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[exp_le_inv_one_sub](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Lower.lean)
-/
@[path]
lemma exp_le_inv_one_sub
  {u : ℝ}
-- given
  (h0 : 0 ≤ u)
  (h1 : u < 1) :
-- imply
  Real.exp u ≤ 1 / (1 - u) := by
-- proof
  have hsum : Summable (fun k : ℕ => u ^ k / Nat.factorial k) :=
    Real.summable_pow_div_factorial u
  have hgeo : Summable (fun k : ℕ => u ^ k) := by
    apply summable_geometric_of_lt_one
    · positivity
    · simpa using h1
  have hle : (fun k : ℕ => u ^ k / Nat.factorial k) ≤ fun k : ℕ => u ^ k := by
    intro k
    apply div_le_self (pow_nonneg h0 k)
    have h : 1 ≤ Nat.factorial k := Nat.succ_le_of_lt (Nat.factorial_pos k)
    exact_mod_cast h
  have hexp : Real.exp u = ∑' k : ℕ, u ^ k / (Nat.factorial k : ℝ) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  calc Real.exp u = ∑' k : ℕ, u ^ k / Nat.factorial k := hexp
    _ ≤ ∑' k : ℕ, u ^ k := Summable.tsum_le_tsum (fun k => hle k) hsum hgeo
    _ = 1 / (1 - u) := by
      rw [tsum_geometric_of_lt_one h0 h1, one_div]

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[one_sub_inv_le_log](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Lower.lean)
-/
@[path]
lemma one_sub_inv_le_log
  {t : ℝ}
-- given
  (ht : 1 ≤ t) :
-- imply
  1 - 1 / t ≤ Real.log t := by
-- proof
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  rw [Real.le_log_iff_exp_le ht0]
  set u : ℝ := 1 - 1 / t with hu
  have hu0 : 0 ≤ u := by
    rw [hu]
    have : 1 / t ≤ 1 := by
      rwa [div_le_one ht0]
    linarith
  have hu1 : u < 1 := by
    rw [hu]
    have : (0 : ℝ) < 1 / t := by positivity
    linarith
  have htne : t ≠ 0 := ht0.ne'
  calc Real.exp (1 - 1 / t) = Real.exp u := rfl
    _ ≤ 1 / (1 - u) := exp_le_inv_one_sub hu0 hu1
    _ = t := by rw [hu]; field_simp; ring

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[stirling_lower](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Lower.lean)
-/
@[path]
lemma stirling_lower
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  (n : ℝ) ^ n * Real.exp (-(n : ℝ) + 1) ≤ (Nat.factorial n : ℝ) := by
-- proof
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hn0 : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le zero_lt_one hn
    have key : (1 + 1 / (n : ℝ)) ^ n ≤ Real.exp 1 := by
      have hlog : Real.log ((1 + 1 / (n : ℝ)) ^ n) < 1 := by
        rw [Real.log_pow]
        have h1 : Real.log (1 + 1 / (n : ℝ)) < 1 / (n : ℝ) := by
          have h := Real.log_lt_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / n by positivity)
            (show (1 : ℝ) + 1 / n ≠ 1 by
              intro hcon
              have : (1 : ℝ) / n = 0 := by linarith
              simp [hn0.ne'] at this)
          simpa using h
        calc (n : ℝ) * Real.log (1 + 1 / (n : ℝ))
          < (n : ℝ) * (1 / (n : ℝ)) := by gcongr
          _ = 1 := by field_simp
      have hpos : (0 : ℝ) < (1 + 1 / (n : ℝ)) ^ n := by positivity
      have h2 : Real.log ((1 + 1 / (n : ℝ)) ^ n) < Real.log (Real.exp 1) := by
        rwa [Real.log_exp]
      have := (Real.log_lt_log_iff hpos (Real.exp_pos 1)).mp h2
      simpa using this.le
    have hstep : ((n + 1 : ℕ) : ℝ) ^ (n + 1) * Real.exp (-((n + 1 : ℕ) : ℝ) + 1)
      ≤ (n : ℝ) ^ n * Real.exp (-(n : ℝ) + 1) * ((n : ℝ) + 1) := by
      have e1 : Real.exp (-((n + 1 : ℕ) : ℝ) + 1)
        = Real.exp (-(n : ℝ) + 1) / Real.exp 1 := by
        rw [show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by push_cast; ring]
        rw [show -(n + 1 : ℝ) + 1 = (-(n : ℝ) + 1) - 1 by ring, Real.exp_sub]
      rw [e1]
      rw [show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by push_cast; ring]
      rw [pow_succ]
      have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
      rw [show ((n : ℝ) + 1) ^ n * ((n : ℝ) + 1)
        * (Real.exp (-(n : ℝ) + 1) / Real.exp 1)
        = (((n : ℝ) + 1) ^ n * ((n : ℝ) + 1)
          * Real.exp (-(n : ℝ) + 1)) / Real.exp 1 by ring,
        div_le_iff₀ hpos]
      -- goal: (n+1)^n * (n+1) * exp(..) ≤ n^n * exp(..) * (n+1) * exp 1
      have h2 : ((n : ℝ) + 1) ^ n ≤ Real.exp 1 * (n : ℝ) ^ n := by
        have := mul_le_mul_of_nonneg_right key (show (0 : ℝ) ≤ (n : ℝ) ^ n by positivity)
        rwa [show (1 + 1 / (n : ℝ)) ^ n * (n : ℝ) ^ n = ((n : ℝ) + 1) ^ n by
          rw [← mul_pow]
          congr 1
          field_simp] at this
      calc ((n : ℝ) + 1) ^ n * ((n : ℝ) + 1) * Real.exp (-(n : ℝ) + 1)
        ≤ (Real.exp 1 * (n : ℝ) ^ n) * ((n : ℝ) + 1) * Real.exp (-(n : ℝ) + 1) := by
          gcongr
        _ = (n : ℝ) ^ n * Real.exp (-(n : ℝ) + 1) * ((n : ℝ) + 1) * Real.exp 1 := by ring
    calc ((n + 1 : ℕ) : ℝ) ^ (n + 1) * Real.exp (-((n + 1 : ℕ) : ℝ) + 1)
      ≤ (n : ℝ) ^ n * Real.exp (-(n : ℝ) + 1) * ((n : ℝ) + 1) := hstep
      _ ≤ (Nat.factorial n : ℝ) * ((n : ℝ) + 1) := by gcongr
      _ = ((Nat.factorial (n + 1) : ℕ) : ℝ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[stirling_upper](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Lower.lean)
-/
@[path]
lemma stirling_upper
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  (Nat.factorial n : ℝ) ≤ (n : ℝ) ^ (n + 1) * Real.exp (-(n : ℝ) + 1) := by
-- proof
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hn0 : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le zero_lt_one hn
    have key : Real.exp 1 ≤ (1 + 1 / (n : ℝ)) ^ (n + 1) := by
      have ht : (1 : ℝ) ≤ 1 + 1 / (n : ℝ) := by
        have : (0 : ℝ) < 1 / (n : ℝ) := by positivity
        linarith
      have h := one_sub_inv_le_log ht
      have heq : 1 - 1 / (1 + 1 / (n : ℝ)) = 1 / ((n : ℝ) + 1) := by
        field_simp
        ring
      rw [heq] at h
      have hlog : (1 : ℝ) ≤ Real.log ((1 + 1 / (n : ℝ)) ^ (n + 1)) := by
        rw [Real.log_pow]
        push_cast
        calc (1 : ℝ) = ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) := by field_simp
          _ ≤ ((n : ℝ) + 1) * Real.log (1 + 1 / (n : ℝ)) := by gcongr
      have hpos : (0 : ℝ) < (1 + 1 / (n : ℝ)) ^ (n + 1) := by positivity
      have h2 : Real.log (Real.exp 1) ≤ Real.log ((1 + 1 / (n : ℝ)) ^ (n + 1)) := by
        rwa [Real.log_exp]
      have := (Real.log_le_log_iff (Real.exp_pos 1) hpos).mp h2
      simpa using this
    have hstep : ((n : ℝ) + 1) * ((n : ℝ) ^ (n + 1) * Real.exp (-(n : ℝ) + 1))
      ≤ ((n + 1 : ℕ) : ℝ) ^ (n + 1 + 1) * Real.exp (-((n + 1 : ℕ) : ℝ) + 1) := by
      rw [show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by push_cast; ring]
      have e1 : Real.exp (-((n : ℝ) + 1) + 1)
        = Real.exp (-(n : ℝ) + 1) / Real.exp 1 := by
        rw [show -((n : ℝ) + 1) + 1 = (-(n : ℝ) + 1) - 1 by ring, Real.exp_sub]
      rw [e1, pow_succ ((n : ℝ) + 1) (n + 1)]
      have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
      have e2 : ((n : ℝ) + 1) ^ (n + 1) * ((n : ℝ) + 1)
        * (Real.exp (-(n : ℝ) + 1) / Real.exp 1)
        = (((n : ℝ) + 1) ^ (n + 1) * ((n : ℝ) + 1)
          * Real.exp (-(n : ℝ) + 1)) / Real.exp 1 := by ring
      rw [e2, le_div_iff₀ hpos]
      -- goal: (n+1) * (n^{n+1} * exp) * exp 1 ≤ (n+1)^{n+1} * (n+1) * exp
      have h2 : Real.exp 1 * (n : ℝ) ^ (n + 1) ≤ ((n : ℝ) + 1) ^ (n + 1) := by
        have := mul_le_mul_of_nonneg_right key
          (show (0 : ℝ) ≤ (n : ℝ) ^ (n + 1) by positivity)
        rwa [show (1 + 1 / (n : ℝ)) ^ (n + 1) * (n : ℝ) ^ (n + 1) = ((n : ℝ) + 1) ^ (n + 1) by
          rw [← mul_pow]
          congr 1
          field_simp] at this
      calc ((n : ℝ) + 1) * ((n : ℝ) ^ (n + 1) * Real.exp (-(n : ℝ) + 1)) * Real.exp 1
        = ((n : ℝ) + 1) * Real.exp (-(n : ℝ) + 1)
          * (Real.exp 1 * (n : ℝ) ^ (n + 1)) := by ring
        _ ≤ ((n : ℝ) + 1) * Real.exp (-(n : ℝ) + 1) * ((n : ℝ) + 1) ^ (n + 1) := by gcongr
        _ = ((n : ℝ) + 1) ^ (n + 1) * ((n : ℝ) + 1) * Real.exp (-(n : ℝ) + 1) := by ring
    calc ((Nat.factorial (n + 1) : ℕ) : ℝ) = ((n : ℝ) + 1) * (Nat.factorial n : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
      _ ≤ ((n : ℝ) + 1) * ((n : ℝ) ^ (n + 1) * Real.exp (-(n : ℝ) + 1)) := by gcongr
      _ ≤ ((n + 1 : ℕ) : ℝ) ^ (n + 1 + 1) * Real.exp (-((n + 1 : ℕ) : ℝ) + 1) := hstep
open Nat Finset

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[Q9_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Lower.lean)
-/
@[path]
lemma Q9_pos :
-- imply
  0 < Q9 := by
-- proof
unfold Q9; norm_num

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[Q9_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Lower.lean)
-/
@[path]
lemma Q9_eq :
-- imply
  Q9 = 210 :=
-- proof
  rfl

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[Q9div_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Lower.lean)
-/
@[path]
lemma Q9div_pos
  {m : ℕ}
-- given
  (hm1 : 1 ≤ m)
  (hd : m ∣ Q9) :
-- imply
  1 ≤ Q9 / m := by
-- proof
  have hle : m ≤ Q9 := Nat.le_of_dvd Q9_pos hd
  have hpos : 0 < Q9 / m := Nat.div_pos hle (by omega)
  omega

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[N10_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Lower.lean)
-/
@[path]
lemma N10_pos
  {m n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hm1 : 1 ≤ m)
  (hd : m ∣ Q9) :
-- imply
  1 ≤ N10m m n := by
-- proof
  have hqm := Q9div_pos hm1 hd
  unfold N10m
  have h10 : (1:ℕ) ≤ 10 := by norm_num
  calc (1:ℕ) = 1*1*1 := by norm_num
    _ ≤ 10*n*(Q9/m) := Nat.mul_le_mul (Nat.mul_le_mul h10 hn) hqm

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[N9_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Lower.lean)
-/
@[path]
lemma N9_pos
  {m n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hm1 : 1 ≤ m)
  (hd : m ∣ Q9) :
-- imply
  1 ≤ N9m m n := by
-- proof
  have hqm := Q9div_pos hm1 hd
  unfold N9m
  have h9 : (1:ℕ) ≤ 9 := by norm_num
  calc (1:ℕ) = 1*1*1 := by norm_num
    _ ≤ 9*n*(Q9/m) := Nat.mul_le_mul (Nat.mul_le_mul h9 hn) hqm

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[N1_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Lower.lean)
-/
@[path]
lemma N1_pos
  {m n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hm1 : 1 ≤ m)
  (hd : m ∣ Q9) :
-- imply
  1 ≤ N1m m n := by
-- proof
  have hqm := Q9div_pos hm1 hd
  unfold N1m
  calc (1:ℕ) = 1*1 := by norm_num
    _ ≤ n*(Q9/m) := Nat.mul_le_mul hn hqm

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[N10_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Lower.lean)
-/
@[path]
lemma N10_le
  {m n : ℕ} :
-- imply
  N10m m n ≤ 10 * Q9 * n := by
-- proof
  unfold N10m
  have hqm : Q9 / m ≤ Q9 := Nat.div_le_self _ _
  calc 10*n*(Q9/m) ≤ 10*n*Q9 := by gcongr
    _ = 10*Q9*n := by ring

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[N9_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Lower.lean)
-/
@[path]
lemma N9_le
  {m n : ℕ} :
-- imply
  N9m m n ≤ 10 * Q9 * n := by
-- proof
  unfold N9m
  have hqm : Q9 / m ≤ Q9 := Nat.div_le_self _ _
  have h1 : 9*n*(Q9/m) ≤ 9*n*Q9 := by gcongr
  have h2 : 9*n*Q9 ≤ 10*Q9*n := by
    have h9 : (9:ℕ) ≤ 10 := by norm_num
    have e2 : 9*(n*Q9) ≤ 10*(n*Q9) := Nat.mul_le_mul h9 (le_refl _)
    have r1 : 9*n*Q9 = 9*(n*Q9) := by ring
    have r4 : (10:ℕ)*Q9*n = 10*(n*Q9) := by ring
    rwa [r1, r4]
  exact le_trans h1 h2

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[N1_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Lower.lean)
-/
@[path]
lemma N1_le
  {m n : ℕ} :
-- imply
  N1m m n ≤ 10 * Q9 * n := by
-- proof
  unfold N1m
  have hqm : Q9 / m ≤ Q9 := Nat.div_le_self _ _
  have h1 : n*(Q9/m) ≤ n*Q9 := by gcongr
  have h2 : n*Q9 ≤ 10*Q9*n := by
    calc n*Q9 = (n*Q9)*1 := by ring
      _ ≤ (n*Q9)*10 := Nat.mul_le_mul (le_refl _) (by norm_num)
      _ = 10*Q9*n := by ring
  exact le_trans h1 h2

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[Nadd9](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Lower.lean)
-/
@[path]
lemma Nadd9
  {m n : ℕ}
-- given
  (hm1 : 1 ≤ m)
  (hd : m ∣ Q9) :
-- imply
  N10m m n = N9m m n + N1m m n := by
-- proof
  obtain ⟨k, hk⟩ := hd
  have hqm : Q9 / m = k := by
    rw [hk, Nat.mul_div_cancel_left _ hm1]
  unfold N10m N9m N1m
  rw [hqm]
  ring

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[ratio9_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Lower.lean)
-/
@[path]
lemma ratio9_dvd
  {m n : ℕ}
-- given
  (hm1 : 1 ≤ m)
  (hd : m ∣ Q9) :
-- imply
  (N9m m n)! * (N1m m n)! ∣ (N10m m n)! := by
-- proof
  have h := Nadd9 (n := n) hm1 hd
  have e := Nat.factorial_mul_factorial_dvd_factorial_add (N9m m n) (N1m m n)
  rwa [← h] at e

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[ratio9_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Lower.lean)
-/
@[path]
lemma ratio9_pos
  {m n : ℕ}
-- given
  (_hn : 1 ≤ n)
  (hm1 : 1 ≤ m)
  (hd : m ∣ Q9) :
-- imply
  0 < ratio9 m n := by
-- proof
  unfold ratio9
  apply Nat.div_pos (Nat.le_of_dvd (Nat.factorial_pos _) (ratio9_dvd m n hm1 hd))
  positivity

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[log_ratio9](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Lower.lean)
-/
@[path]
lemma log_ratio9
  {m n : ℕ}
-- given
  (_hn : 1 ≤ n)
  (hm1 : 1 ≤ m)
  (hd : m ∣ Q9) :
-- imply
  Real.log ((ratio9 m n : ℕ) : ℝ) = Real.log (((N10m m n)!) : ℝ) - Real.log (((N9m m n)!) : ℝ) - Real.log (((N1m m n)!) : ℝ) := by
-- proof
  have hdvd := ratio9_dvd m n hm1 hd
  have hpos : 0 < (N9m m n)! * (N1m m n)! := by positivity
  have hne : (((N9m m n)! * (N1m m n)! : ℕ) : ℝ) ≠ 0 := by
    have hposR : (0:ℝ) < (((N9m m n)! * (N1m m n)! : ℕ) : ℝ) := by positivity
    exact ne_of_gt hposR
  have hcast : ((ratio9 m n : ℕ) : ℝ)
    = ((N10m m n)! : ℝ) / (((N9m m n)! : ℝ) * ((N1m m n)! : ℝ)) := by
    unfold ratio9
    rw [Nat.cast_div hdvd hne, Nat.cast_mul]
  rw [hcast, Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity)
    (by positivity)]
  ring

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[w9_mu_sum_Q](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Lower.lean)
-/
@[path]
lemma w9_mu_sum_Q :
-- imply
  w9.toFinset.sum (fun q : ℕ × ℤ => (q.2 : ℚ) / (q.1 : ℚ)) = 8/35 := by
-- proof
  have hlist :
    (w9.map (fun q : ℕ × ℤ => (q.2 : ℚ) / (q.1 : ℚ))).sum = 8 / 35 := by
    unfold w9
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    norm_num
  rwa [← map_sum_toFinset w9 w9_nodup]

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[w9_mu_sum_R](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Lower.lean)
-/
@[path]
lemma w9_mu_sum_R :
-- imply
  w9.toFinset.sum (fun q : ℕ × ℤ => (q.2 : ℝ) / (q.1 : ℝ)) = 8/35 := by
-- proof
  have h := w9_mu_sum_Q
  have hcast : ((w9.toFinset.sum (fun q : ℕ × ℤ => (q.2 : ℚ) / (q.1 : ℚ)) : ℚ) : ℝ)
    = w9.toFinset.sum (fun q : ℕ × ℤ => (q.2 : ℝ) / (q.1 : ℝ)) := by
    push_cast
    rfl
  rw [h] at hcast
  have h8 : (((8/35 : ℚ)) : ℝ) = (8/35 : ℝ) := by norm_num
  rwa [h8] at hcast

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[log_fact_lower](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Lower.lean)
-/
@[path]
lemma log_fact_lower
  {N : ℕ}
-- given
  (hN : 1 ≤ N) :
-- imply
  (N : ℝ) * Real.log (N : ℝ) - (N : ℝ) + 1 ≤ Real.log ((N ! : ℕ) : ℝ) := by
-- proof
  have hN0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have h := stirling_lower hN
  have hpos : (0:ℝ) < (N : ℝ)^N * Real.exp (-(N:ℝ)+1) := by positivity
  have hlog := Real.log_le_log hpos h
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_exp] at hlog
  linarith [hlog]

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[log_fact_upper](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Lower.lean)
-/
@[path]
lemma log_fact_upper
  {N : ℕ}
-- given
  (hN : 1 ≤ N) :
-- imply
  Real.log ((N ! : ℕ) : ℝ) ≤ ((N : ℝ)+1) * Real.log (N : ℝ) - (N : ℝ) + 1 := by
-- proof
  have hN0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have h := stirling_upper hN
  have hpos : (0:ℝ) < ((N ! : ℕ) : ℝ) := by positivity
  have hlog := Real.log_le_log hpos h
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_exp] at hlog
  push_cast at hlog
  linarith [hlog]

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[logF9_term_lower](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Lower.lean)
-/
@[path]
lemma logF9_term_lower
  {q : ℕ × ℤ}
  {n : ℕ}
-- given
  (hq : q ∈ w9)
  (hn : 1 ≤ n) :
-- imply
  (q.2 : ℝ) * (Real.log (((N10m q.1 n)!) : ℝ) - Real.log (((N9m q.1 n)!) : ℝ) - Real.log (((N1m q.1 n)!) : ℝ)) ≥ (q.2 : ℝ) * (fmain ((N10m q.1 n : ℕ) : ℝ) - fmain ((N9m q.1 n : ℕ) : ℝ) - fmain ((N1m q.1 n : ℕ) : ℝ)) - (1 + Real.log ((N10m q.1 n : ℕ) : ℝ) + Real.log ((N9m q.1 n : ℕ) : ℝ) + Real.log ((N1m q.1 n : ℕ) : ℝ)) := by
-- proof
  have hm1 : 1 ≤ q.1 := w9_pos q hq
  have hd : q.1 ∣ Q9 := w9_dvd q hq
  have hA : 1 ≤ N10m q.1 n := N10_pos hn hm1 hd
  have hB : 1 ≤ N9m q.1 n := N9_pos hn hm1 hd
  have hC : 1 ≤ N1m q.1 n := N1_pos hn hm1 hd
  have sAL := log_fact_lower hA
  have sAU := log_fact_upper hA
  have sBL := log_fact_lower hB
  have sBU := log_fact_upper hB
  have sCL := log_fact_lower hC
  have sCU := log_fact_upper hC
  have hA0 : (0:ℝ) ≤ Real.log ((N10m q.1 n : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hA)
  have hB0 : (0:ℝ) ≤ Real.log ((N9m q.1 n : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hB)
  have hC0 : (0:ℝ) ≤ Real.log ((N1m q.1 n : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hC)
  have hsign := w9_mu_sign q hq
  unfold fmain
  obtain h1 | hm1sgn := hsign
  · have hmu : (q.2 : ℝ) = 1 := by exact_mod_cast h1
    rw [hmu, one_mul, one_mul]
    linarith [sAL, sBU, sCU, hA0]
  · have hmu : (q.2 : ℝ) = -1 := by exact_mod_cast hm1sgn
    rw [hmu]
    linarith [sAU, sBL, sCL, hB0, hC0]

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[CNdvd9](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Lower.lean)
-/
@[path]
lemma CNdvd9
  {C : ℕ}
  {q : ℕ × ℤ}
  {n : ℕ}
-- given
  (hC : Q9 ∣ C)
  (hq : q ∈ w9) :
-- imply
  q.1 ∣ C * n :=
-- proof
  dvd_trans (w9_dvd q hq) (dvd_trans hC (Nat.dvd_mul_right C n))

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[Z9_value](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Lower.lean)
-/
@[path]
lemma Z9_value
  {C n : ℕ}
-- given
  (hC0 : 0 < C)
  (hn : 1 ≤ n)
  (hC : Q9 ∣ C) :
-- imply
  w9.toFinset.sum (fun q : ℕ × ℤ => (q.2 : ℝ) * fmain (((C*n/q.1 : ℕ)) : ℝ)) = (8/35) * ((C*n : ℕ):ℝ) * (Real.log ((C*n : ℕ):ℝ) - 1) - K9 * ((C*n : ℕ):ℝ) := by
-- proof
  have hterm : ∀ q ∈ w9.toFinset, (q.2:ℝ) * fmain (((C*n/q.1:ℕ)):ℝ)
    = ((C*n:ℕ):ℝ) * Real.log ((C*n:ℕ):ℝ) * ((q.2:ℝ)/(q.1:ℝ))
      - ((C*n:ℕ):ℝ) * ((q.2:ℝ) * Real.log (q.1:ℝ) / (q.1:ℝ))
      - ((C*n:ℕ):ℝ) * ((q.2:ℝ)/(q.1:ℝ)) := by
    intro q hq
    have hqmem : q ∈ w9 := List.mem_toFinset.mp hq
    have hm1 : 1 ≤ q.1 := w9_pos q hqmem
    have hdvd : q.1 ∣ C*n := CNdvd9 C hC q hqmem n
    have hm0 : (q.1:ℝ) ≠ 0 := by exact_mod_cast (show q.1 ≠ 0 by omega)
    have hCn0 : ((C*n:ℕ):ℝ) ≠ 0 := by
      have hpos : 0 < C*n := Nat.mul_pos hC0 (by omega)
      exact_mod_cast (ne_of_gt hpos)
    have hcast : (((C*n/q.1:ℕ)):ℝ) = ((C*n:ℕ):ℝ)/(q.1:ℝ) :=
      Nat.cast_div hdvd (by exact_mod_cast (show q.1 ≠ 0 by omega))
    unfold fmain
    rw [hcast, Real.log_div hCn0 hm0]
    field_simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hA : (w9.toFinset.sum fun q : ℕ×ℤ =>
    ((C*n:ℕ):ℝ) * Real.log ((C*n:ℕ):ℝ) * ((q.2:ℝ)/(q.1:ℝ)))
    = ((C*n:ℕ):ℝ) * Real.log ((C*n:ℕ):ℝ) * (8/35) := by
    rw [← Finset.mul_sum, w9_mu_sum_R]
  have hB : (w9.toFinset.sum fun q : ℕ×ℤ =>
    ((C*n:ℕ):ℝ) * ((q.2:ℝ) * Real.log (q.1:ℝ) / (q.1:ℝ)))
    = ((C*n:ℕ):ℝ) * K9 := by
    rw [← Finset.mul_sum]
    rfl
  have hC : (w9.toFinset.sum fun q : ℕ×ℤ => ((C*n:ℕ):ℝ) * ((q.2:ℝ)/(q.1:ℝ)))
    = ((C*n:ℕ):ℝ) * (8/35) := by
    rw [← Finset.mul_sum, w9_mu_sum_R]
  rw [hA, hB, hC]
  ring

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[N10_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Lower.lean)
-/
@[path]
lemma N10_eq
  {m n : ℕ}
-- given
  (hm1 : 1 ≤ m)
  (hd : m ∣ Q9) :
-- imply
  N10m m n = 10*Q9*n/m := by
-- proof
  obtain ⟨k, hk⟩ := hd
  unfold N10m
  have hqm : Q9/m = k := by rw [hk, Nat.mul_div_cancel_left _ hm1]
  rw [hqm, hk, show 10*(m*k)*n = m*(10*n*k) by ring, Nat.mul_div_cancel_left _ hm1]

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[N9_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Lower.lean)
-/
@[path]
lemma N9_eq
  {m n : ℕ}
-- given
  (hm1 : 1 ≤ m)
  (hd : m ∣ Q9) :
-- imply
  N9m m n = 9*Q9*n/m := by
-- proof
  obtain ⟨k, hk⟩ := hd
  unfold N9m
  have hqm : Q9/m = k := by rw [hk, Nat.mul_div_cancel_left _ hm1]
  rw [hqm, hk, show 9*(m*k)*n = m*(9*n*k) by ring, Nat.mul_div_cancel_left _ hm1]

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[N1_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Lower.lean)
-/
@[path]
lemma N1_eq
  {m n : ℕ}
-- given
  (hm1 : 1 ≤ m)
  (hd : m ∣ Q9) :
-- imply
  N1m m n = Q9*n/m := by
-- proof
  obtain ⟨k, hk⟩ := hd
  unfold N1m
  have hqm : Q9/m = k := by rw [hk, Nat.mul_div_cancel_left _ hm1]
  rw [hqm, hk, show (m*k)*n = m*(n*k) by ring, Nat.mul_div_cancel_left _ hm1]

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[Z9_combined](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Lower.lean)
-/
@[path]
lemma Z9_combined
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  w9.toFinset.sum (fun q : ℕ×ℤ => (q.2:ℝ) * (fmain (((10*Q9*n/q.1:ℕ)):ℝ) - fmain (((9*Q9*n/q.1:ℕ)):ℝ) - fmain (((Q9*n/q.1:ℕ)):ℝ))) = 48 * (n:ℝ) * (10 * Real.log 10 - 9 * Real.log 9) := by
-- proof
  have hsplit : ∀ q ∈ w9.toFinset, (q.2:ℝ) * (fmain (((10*Q9*n/q.1:ℕ)):ℝ)
    - fmain (((9*Q9*n/q.1:ℕ)):ℝ) - fmain (((Q9*n/q.1:ℕ)):ℝ))
    = (q.2:ℝ)*fmain (((10*Q9*n/q.1:ℕ)):ℝ)
      - (q.2:ℝ)*fmain (((9*Q9*n/q.1:ℕ)):ℝ)
      - (q.2:ℝ)*fmain (((Q9*n/q.1:ℕ)):ℝ) := by
    intro q _; ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Z9_value (10*Q9) n (by rw [Q9_eq]; norm_num) hn (Nat.dvd_mul_left Q9 10),
    Z9_value (9*Q9) n (by rw [Q9_eq]; norm_num) hn (Nat.dvd_mul_left Q9 9),
    Z9_value Q9 n Q9_pos hn (dvd_refl Q9)]
  have hQn0 : ((Q9*n:ℕ):ℝ) ≠ 0 := by
    have hpos : 0 < Q9*n := Nat.mul_pos Q9_pos (by omega)
    exact_mod_cast (ne_of_gt hpos)
  have e10 : Real.log (((10*Q9*n:ℕ)):ℝ)
    = Real.log 10 + Real.log (((Q9*n:ℕ)):ℝ) := by
    have heq : (((10*Q9*n:ℕ)):ℝ) = 10 * (((Q9*n:ℕ)):ℝ) := by push_cast; ring
    rw [heq, Real.log_mul (by norm_num) hQn0]
  have e9 : Real.log (((9*Q9*n:ℕ)):ℝ)
    = Real.log 9 + Real.log (((Q9*n:ℕ)):ℝ) := by
    have heq : (((9*Q9*n:ℕ)):ℝ) = 9 * (((Q9*n:ℕ)):ℝ) := by push_cast; ring
    rw [heq, Real.log_mul (by norm_num) hQn0]
  rw [e10, e9, Q9_eq]
  push_cast
  ring_nf

end MathlibExt.NumberTheory.BreuschWanted.Internal

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/--
[logF9_lower](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Lower.lean)
-/
@[path]
lemma logF9_lower
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  48 * (n:ℝ) * (10 * Real.log 10 - 9 * Real.log 9) - 16 - 48 * Real.log ((2100*n:ℕ):ℝ) ≤ logF9 n := by
-- proof
  have hterm : ∀ q ∈ w9.toFinset,
    (q.2:ℝ) * Real.log ((ratio9 q.1 n:ℕ):ℝ)
    ≥ (q.2:ℝ) * (fmain ((N10m q.1 n:ℕ):ℝ) - fmain ((N9m q.1 n:ℕ):ℝ)
      - fmain ((N1m q.1 n:ℕ):ℝ))
      - (1 + Real.log ((N10m q.1 n:ℕ):ℝ) + Real.log ((N9m q.1 n:ℕ):ℝ)
        + Real.log ((N1m q.1 n:ℕ):ℝ)) := by
    intro q hq
    have hqmem : q ∈ w9 := List.mem_toFinset.mp hq
    have hm1 : 1 ≤ q.1 := w9_pos q hqmem
    have hd : q.1 ∣ Q9 := w9_dvd q hqmem
    have hlog := log_ratio9 q.1 n hn hm1 hd
    rw [hlog]
    exact logF9_term_lower q hqmem n hn
  have hsum := Finset.sum_le_sum hterm
  have hsum2 : w9.toFinset.sum (fun q : ℕ×ℤ => (q.2:ℝ)
    * (fmain ((N10m q.1 n:ℕ):ℝ) - fmain ((N9m q.1 n:ℕ):ℝ)
      - fmain ((N1m q.1 n:ℕ):ℝ))
    - (1 + Real.log ((N10m q.1 n:ℕ):ℝ) + Real.log ((N9m q.1 n:ℕ):ℝ)
      + Real.log ((N1m q.1 n:ℕ):ℝ)))
    ≤ logF9 n := hsum
  rw [Finset.sum_sub_distrib] at hsum2
  have hbridge : w9.toFinset.sum (fun q : ℕ×ℤ => (q.2:ℝ)
    * (fmain ((N10m q.1 n:ℕ):ℝ) - fmain ((N9m q.1 n:ℕ):ℝ)
      - fmain ((N1m q.1 n:ℕ):ℝ)))
    = w9.toFinset.sum (fun q : ℕ×ℤ => (q.2:ℝ) * (fmain (((10*Q9*n/q.1:ℕ)):ℝ)
      - fmain (((9*Q9*n/q.1:ℕ)):ℝ) - fmain (((Q9*n/q.1:ℕ)):ℝ))) := by
    apply Finset.sum_congr rfl
    intro q hq
    have hqmem : q ∈ w9 := List.mem_toFinset.mp hq
    have hm1 : 1 ≤ q.1 := w9_pos q hqmem
    have hd : q.1 ∣ Q9 := w9_dvd q hqmem
    rw [N10_eq hm1 hd, N9_eq hm1 hd, N1_eq hm1 hd]
  rw [hbridge, Z9_combined n hn] at hsum2
  have herr : w9.toFinset.sum (fun q : ℕ×ℤ => (1:ℝ)
    + Real.log ((N10m q.1 n:ℕ):ℝ) + Real.log ((N9m q.1 n:ℕ):ℝ)
    + Real.log ((N1m q.1 n:ℕ):ℝ))
    ≤ 16 + 48 * Real.log ((2100*n:ℕ):ℝ) := by
    have hcard : w9.toFinset.card = 16 := by
      rw [List.toFinset_card_of_nodup w9_nodup, w9_length]
    have h1 : ∀ q ∈ w9.toFinset, (1:ℝ) + Real.log ((N10m q.1 n:ℕ):ℝ)
      + Real.log ((N9m q.1 n:ℕ):ℝ) + Real.log ((N1m q.1 n:ℕ):ℝ)
      ≤ 1 + 3 * Real.log ((2100*n:ℕ):ℝ) := by
      intro q hq
      have hA : Real.log ((N10m q.1 n:ℕ):ℝ) ≤ Real.log ((2100*n:ℕ):ℝ) := by
        have hA1 : 1 ≤ N10m q.1 n := by
          have hqmem : q ∈ w9 := List.mem_toFinset.mp hq
          exact N10_pos hn (w9_pos q hqmem) (w9_dvd q hqmem)
        have hA0 : (0:ℝ) < ((N10m q.1 n:ℕ):ℝ) := by
          exact_mod_cast (lt_of_lt_of_le zero_lt_one hA1)
        apply Real.log_le_log hA0
        have hle : N10m q.1 n ≤ 2100*n := by
          have h := N10_le (m := q.1) (n := n)
          rw [Q9_eq] at h
          have he : (10:ℕ)*210*n = 2100*n := by ring
          rw [he] at h; exact h
        exact_mod_cast hle
      have hB : Real.log ((N9m q.1 n:ℕ):ℝ) ≤ Real.log ((2100*n:ℕ):ℝ) := by
        have hB1 : 1 ≤ N9m q.1 n := by
          have hqmem : q ∈ w9 := List.mem_toFinset.mp hq
          exact N9_pos hn (w9_pos q hqmem) (w9_dvd q hqmem)
        have hB0 : (0:ℝ) < ((N9m q.1 n:ℕ):ℝ) := by
          exact_mod_cast (lt_of_lt_of_le zero_lt_one hB1)
        apply Real.log_le_log hB0
        have hle : N9m q.1 n ≤ 2100*n := by
          have h := N9_le (m := q.1) (n := n)
          rw [Q9_eq] at h
          have he : (10:ℕ)*210*n = 2100*n := by ring
          rw [he] at h; exact h
        exact_mod_cast hle
      have hC : Real.log ((N1m q.1 n:ℕ):ℝ) ≤ Real.log ((2100*n:ℕ):ℝ) := by
        have hC1 : 1 ≤ N1m q.1 n := by
          have hqmem : q ∈ w9 := List.mem_toFinset.mp hq
          exact N1_pos hn (w9_pos q hqmem) (w9_dvd q hqmem)
        have hC0 : (0:ℝ) < ((N1m q.1 n:ℕ):ℝ) := by
          exact_mod_cast (lt_of_lt_of_le zero_lt_one hC1)
        apply Real.log_le_log hC0
        have hle : N1m q.1 n ≤ 2100*n := by
          have h := N1_le (m := q.1) (n := n)
          rw [Q9_eq] at h
          have he : (10:ℕ)*210*n = 2100*n := by ring
          rw [he] at h; exact h
        exact_mod_cast hle
      linarith [hA, hB, hC]
    calc w9.toFinset.sum (fun q : ℕ×ℤ => (1:ℝ) + Real.log ((N10m q.1 n:ℕ):ℝ)
      + Real.log ((N9m q.1 n:ℕ):ℝ) + Real.log ((N1m q.1 n:ℕ):ℝ))
      ≤ w9.toFinset.sum (fun _ => (1:ℝ) + 3*Real.log ((2100*n:ℕ):ℝ)) :=
        Finset.sum_le_sum h1
      _ = 16 * (1 + 3*Real.log ((2100*n:ℕ):ℝ)) := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]; norm_num
      _ = 16 + 48*Real.log ((2100*n:ℕ):ℝ) := by ring
  linarith [hsum2, herr]

end MathlibExt.NumberTheory.BreuschWanted.Internal


-- created on 2026-10-23
-- updated on 2026-10-28
