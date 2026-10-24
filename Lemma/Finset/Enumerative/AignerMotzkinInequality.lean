import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.AignerMotzkinInequality
open scoped BigOperators
open MetaMathlibExt


namespace MetaMathlibExt

/--
[Mot_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma Mot_pos (r : ℕ) : 0 < Mot r := by
  unfold Mot
  have h0mem : 0 ∈ Finset.range (r / 2 + 1) := by simp
  have h1 : (Nat.choose (2 * 0) 0 / (0 + 1)) * Nat.choose r (2 * 0) = 1 := by simp
  calc 0 < 1 := by norm_num
    _ = (Nat.choose (2 * 0) 0 / (0 + 1)) * Nat.choose r (2 * 0) := h1.symm
    _ ≤ ∑ k ∈ Finset.range (r / 2 + 1),
      (Nat.choose (2 * k) k / (k + 1)) * Nat.choose r (2 * k) := by
        exact Finset.single_le_sum
          (f := fun k => (Nat.choose (2 * k) k / (k + 1)) * Nat.choose r (2 * k))
          (fun k _ => Nat.zero_le _) h0mem

end MetaMathlibExt

namespace MetaMathlibExt

/--
[fact_step2](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma fact_step2 (K : ℕ) (hK2 : 2 ≤ K) :
  K.factorial = K * ((K - 1) * (K - 2).factorial) := by
  have hKeq : K = (K - 2) + 2 := by omega
  conv_lhs => rw [hKeq]
  have e1 : ((K - 2) + 2) = ((K - 2) + 1) + 1 := by omega
  rw [e1, Nat.factorial_succ, Nat.factorial_succ]
  have h1 : (K - 2) + 1 + 1 = K := by omega
  have h2 : (K - 2) + 1 = K - 1 := by omega
  rw [h1, h2]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[fact_up2](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma fact_up2 (A : ℕ) : (A + 2).factorial = (A + 2) * ((A + 1) * A.factorial) := by
  rw [show A + 2 = (A + 1) + 1 from by omega, Nat.factorial_succ, Nat.factorial_succ]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[choose_step2_Q](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma choose_step2_Q (N K : ℕ) (hK : K ≤ N) (hK2 : 2 ≤ K) :
  ((Nat.choose N (K - 2) : ℕ) : ℚ)
    = ((Nat.choose N K : ℕ) : ℚ) * ((K : ℚ) * (((K - 1 : ℕ)) : ℚ))
      / (((N - K + 2 : ℕ) : ℚ) * (((N - K + 1 : ℕ)) : ℚ)) := by
  have hK2le : K - 2 ≤ N := by omega
  have hNKeq : N - (K - 2) = (N - K) + 2 := by omega
  have e1 := Nat.choose_eq_factorial_div_factorial hK (n := N) (k := K)
  have e2 := Nat.choose_eq_factorial_div_factorial hK2le (n := N) (k := K - 2)
  have c1 : ((Nat.choose N K : ℕ) : ℚ)
    = (N.factorial : ℚ) / ((K.factorial : ℚ) * (((N - K).factorial : ℚ))) := by
    rw [e1]
    rw [Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial hK) (by positivity)]
    push_cast
    ring
  have c2 : ((Nat.choose N (K - 2) : ℕ) : ℚ)
    = (N.factorial : ℚ) / ((((K - 2).factorial : ℚ)) * ((((N - (K - 2)).factorial : ℚ)))) := by
    rw [e2]
    rw [Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial hK2le) (by positivity)]
    push_cast
    ring
  rw [c1, c2, hNKeq]
  have fK := fact_step2 K hK2
  have fKc : ((K.factorial : ℕ) : ℚ) = ((K : ℕ) : ℚ) *
    ((((K - 1 : ℕ)) : ℚ) * ((((K - 2).factorial : ℕ)) : ℚ)) := by
    exact_mod_cast fK
  have fNKc : ((((N - K + 2 : ℕ)).factorial : ℕ) : ℚ)
    = (((N - K + 2 : ℕ)) : ℚ) * ((((N - K + 1 : ℕ)) : ℚ) * ((((N - K).factorial : ℕ)) : ℚ)) := by
    exact_mod_cast fact_up2 (N - K)
  rw [fKc, fNKc]
  have hKne : ((K : ℕ) : ℚ) ≠ 0 := by
    have : 0 < K := by omega
    positivity
  have hK1ne : ((((K - 1 : ℕ))) : ℚ) ≠ 0 := by
    have : 0 < K - 1 := by omega
    positivity
  have hN1 : ((((N - K + 2 : ℕ))) : ℚ) ≠ 0 := by
    have : 0 < N - K + 2 := by omega
    positivity
  have hN2 : ((((N - K + 1 : ℕ))) : ℚ) ≠ 0 := by
    have : 0 < N - K + 1 := by omega
    positivity
  have hNpos : (N.factorial : ℚ) ≠ 0 := by positivity
  have hK2f : ((((K - 2).factorial : ℕ)) : ℚ) ≠ 0 := by positivity
  have hNKf : ((((N - K).factorial : ℕ)) : ℚ) ≠ 0 := by positivity
  field_simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[catalan_succ_Q](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma catalan_succ_Q (k : ℕ) :
  ((catalan (k + 1) : ℕ) : ℚ) = ((catalan k : ℕ) : ℚ) * (2 * ((2 * k + 1 : ℕ) : ℚ)) /
    (((k + 2 : ℕ)) : ℚ) := by
  have e1 : (k + 1) * catalan k = k.centralBinom := succ_mul_catalan_eq_centralBinom k
  have e2 : (k + 1 + 1) * catalan (k + 1) = (k + 1).centralBinom := succ_mul_catalan_eq_centralBinom
    (k + 1)
  have e3 : (k + 1) * (k + 1).centralBinom = 2 * (2 * k + 1) * k.centralBinom :=
    Nat.succ_mul_centralBinom_succ k
  have c1 : ((k + 1 : ℕ) : ℚ) * ((catalan k : ℕ) : ℚ) =
    ((k.centralBinom : ℕ) : ℚ) := by exact_mod_cast e1
  have c2 : ((((k + 2 : ℕ))) : ℚ) * ((catalan (k + 1) : ℕ) : ℚ) =
    ((((k + 1).centralBinom : ℕ)) : ℚ) := by
    have : k + 1 + 1 = k + 2 := by omega
    rw [this] at e2
    exact_mod_cast e2
  have c3 : ((k + 1 : ℕ) : ℚ) * ((((k + 1).centralBinom : ℕ)) : ℚ)
    = 2 * (((2 * k + 1 : ℕ)) : ℚ) * (((k.centralBinom : ℕ)) : ℚ) := by exact_mod_cast e3
  have hne2 : ((((k + 2 : ℕ))) : ℚ) ≠ 0 := by positivity
  have hne1 : ((k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hA : ((((k + 1).centralBinom : ℕ)) : ℚ) = 2 * (((2 * k + 1 : ℕ)) : ℚ) *
    ((catalan k : ℕ) : ℚ) := by
    have hmul : ((k + 1 : ℕ) : ℚ) * ((((k + 1).centralBinom : ℕ)) : ℚ)
      = ((k + 1 : ℕ) : ℚ) * (2 * (((2 * k + 1 : ℕ)) : ℚ) * ((catalan k : ℕ) : ℚ)) := by
      linear_combination c3 - 2 * (((2 * k + 1 : ℕ)) : ℚ) * c1
    exact mul_left_cancel₀ hne1 hmul
  rw [eq_div_iff hne2]
  linear_combination c2 + hA

end MetaMathlibExt

namespace MetaMathlibExt

/--
[choose_succ_Q](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma choose_succ_Q (m k : ℕ) (h : 2 * k ≤ m + 1) :
  ((Nat.choose (m + 2) (2 * k) : ℕ) : ℚ)
    = ((Nat.choose (m + 1) (2 * k) : ℕ) : ℚ) * ((m + 2 : ℕ) : ℚ) /
      (((m + 2 - 2 * k : ℕ)) : ℚ) := by
  have hnat : Nat.choose (m + 1) (2 * k) * (m + 2) = Nat.choose (m + 2) (2 * k) *
    (m + 2 - 2 * k) := by
    have h0 := Nat.choose_mul_succ_eq (m + 1) (2 * k)
    simpa using h0
  have hcast : ((Nat.choose (m + 1) (2 * k) : ℕ) : ℚ) * ((m + 2 : ℕ) : ℚ)
    = ((Nat.choose (m + 2) (2 * k) : ℕ) : ℚ) * (((m + 2 - 2 * k : ℕ)) : ℚ) := by
    exact_mod_cast hnat
  have hne : (((m + 2 - 2 * k : ℕ)) : ℚ) ≠ 0 := by
    have : m + 2 - 2 * k ≥ 1 := by omega
    positivity
  field_simp
  linarith [hcast]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[choose_pred_Q](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma choose_pred_Q (m k : ℕ) (h : 2 * k ≤ m + 1) :
  ((Nat.choose m (2 * k) : ℕ) : ℚ)
    = ((Nat.choose (m + 1) (2 * k) : ℕ) : ℚ) * (((m + 1 - 2 * k : ℕ)) : ℚ) /
      ((m + 1 : ℕ) : ℚ) := by
  obtain rfl | hmpos := Nat.eq_zero_or_pos m
  · simp at h
    have hk : k = 0 := by omega
    subst hk
    simp
  · have hnat : Nat.choose m (2 * k) * (m + 1) = Nat.choose (m + 1) (2 * k) * (m + 1 - 2 * k) := by
    have h0 := Nat.choose_mul_succ_eq m (2 * k)
    simpa using h0
    have hcast : ((Nat.choose m (2 * k) : ℕ) : ℚ) * ((m + 1 : ℕ) : ℚ)
      = ((Nat.choose (m + 1) (2 * k) : ℕ) : ℚ) * (((m + 1 - 2 * k : ℕ)) : ℚ) := by
      exact_mod_cast hnat
    have hne : ((m + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    field_simp
    linarith [hcast]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[H_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma H_succ (n k : ℕ) : H n (k + 1) = -4 * (((n : ℚ)) - 2 * ((k : ℚ))) * t n k :=
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[H_pred](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma H_pred (n k : ℕ) (hk : 1 ≤ k) :
  H n k = -4 * (((n : ℚ)) - 2 * ((((k - 1 : ℕ))) : ℚ)) * t n (k - 1) := by
  obtain _ | j := k
  · omega
  · simp [H]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[t_succ_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma t_succ_ratio (m k : ℕ) (h : 2 * k ≤ m + 1) :
  t (m + 2) k = t (m + 1) k * ((m + 2 : ℕ) : ℚ) / (((m + 2 - 2 * k : ℕ)) : ℚ) := by
  unfold t
  rw [choose_succ_Q m k h]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[t_pred_m_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma t_pred_m_ratio (m k : ℕ) (h : 2 * k ≤ m + 1) :
  t m k = t (m + 1) k * (((m + 1 - 2 * k : ℕ)) : ℚ) / ((m + 1 : ℕ) : ℚ) := by
  unfold t
  rw [choose_pred_Q m k h]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[t_pred_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma t_pred_ratio (m k : ℕ) (hk1 : 1 ≤ k) (h2k : 2 * k ≤ m + 1) :
  t (m + 1) (k - 1) = t (m + 1) k * ((k : ℚ) * (((k + 1 : ℕ)) : ℚ))
    / (((m + 3 - 2 * k : ℕ) : ℚ) * (((m + 2 - 2 * k : ℕ)) : ℚ)) := by
  have hk2 : 2 ≤ 2 * k := by omega
  have hKle : 2 * k ≤ m + 1 := h2k
  have hstep := choose_step2_Q (m + 1) (2 * k) hKle hk2
  have hKsub : 2 * k - 2 = 2 * (k - 1) := by omega
  rw [hKsub] at hstep
  have hcat := catalan_succ_Q (k - 1)
  have hk_eq : (k - 1) + 1 = k := by omega
  rw [hk_eq] at hcat
  have hk1eq : (k - 1) + 2 = k + 1 := by omega
  have h2k1 : 2 * (k - 1) + 1 = 2 * k - 1 := by omega
  rw [hk1eq, h2k1] at hcat
  have hNK1 : m + 1 - 2 * k + 2 = m + 3 - 2 * k := by omega
  have hNK2 : m + 1 - 2 * k + 1 = m + 2 - 2 * k := by omega
  rw [hNK1, hNK2] at hstep
  have hneC : (2 : ℚ) * (((2 * k - 1 : ℕ)) : ℚ) ≠ 0 := by
    have : 0 < 2 * k - 1 := by omega
    have hpos : (0 : ℚ) < (((2 * k - 1 : ℕ)) : ℚ) := by exact_mod_cast this
    positivity
  have hneD : ((((k + 1 : ℕ))) : ℚ) ≠ 0 := by positivity
  have hcat' : ((catalan (k - 1) : ℕ) : ℚ)
    = ((catalan k : ℕ) : ℚ) * (((k + 1 : ℕ)) : ℚ) / (2 * (((2 * k - 1 : ℕ)) : ℚ)) := by
    rw [eq_div_iff hneC]
    rw [eq_div_iff hneD] at hcat
    linear_combination -hcat
  unfold t
  rw [hstep, hcat']
  have hneA : (((m + 3 - 2 * k : ℕ)) : ℚ) ≠ 0 := by
    have : 0 < m + 3 - 2 * k := by omega
    positivity
  have hneB : (((m + 2 - 2 * k : ℕ)) : ℚ) ≠ 0 := by
    have : 0 < m + 2 - 2 * k := by omega
    positivity
  have h2k1ne : (((2 * k - 1 : ℕ)) : ℚ) ≠ 0 := by
    have : 0 < 2 * k - 1 := by omega
    positivity
  have hKcast : (((2 * k : ℕ)) : ℚ) = 2 * (k : ℚ) := by push_cast; ring
  field_simp
  rw [hKcast]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[cat_cast](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma cat_cast (k : ℕ) : ((Nat.choose (2 * k) k / (k + 1) : ℕ) : ℚ) = (catalan k : ℚ) := by
  have h1 : Nat.choose (2 * k) k = k.centralBinom := by
    rw [Nat.centralBinom_eq_two_mul_choose]
  rw [h1, catalan_eq_centralBinom_div]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Mot_cast](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma Mot_cast (r : ℕ) : ((Mot r : ℕ) : ℚ) = ∑ k ∈ Finset.range (r / 2 + 1), t r k := by
  unfold Mot t
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Nat.cast_mul, cat_cast]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[t_eq_zero_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma t_eq_zero_of_lt {r k : ℕ} (h : r < 2 * k) : t r k = 0 := by
  unfold t
  have hz : Nat.choose r (2 * k) = 0 := Nat.choose_eq_zero_of_lt h
  rw [hz]
  simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Mot_extend](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma Mot_extend (m r : ℕ) (hm : r / 2 + 1 ≤ m + 3) :
  ((Mot r : ℕ) : ℚ) = ∑ k ∈ Finset.range (m + 3), t r k := by
  rw [Mot_cast]
  apply Finset.sum_subset (Finset.range_mono hm)
  intro k _ hk
  simp only [Finset.mem_range, not_lt] at hk
  have h2k : r < 2 * k := by omega
  exact t_eq_zero_of_lt h2k

end MetaMathlibExt

namespace MetaMathlibExt

/--
[H_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma H_zero (n : ℕ) : H n 0 = 0 :=
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[t_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma t_zero (r : ℕ) : t r 0 = 1 := by
  unfold t
  simp [catalan_zero]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[per_k_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma per_k_zero (m : ℕ) :
  ((m + 4 : ℕ) : ℚ) * t (m + 2) 0 - ((2 * m + 5 : ℕ) : ℚ) * t (m + 1) 0
    - ((3 * (m + 1) : ℕ) : ℚ) * t m 0
    = H (m + 1) 1 - H (m + 1) 0 := by
  rw [t_zero, t_zero, t_zero, H_succ, H_zero, t_zero]
  push_cast
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[per_k_main](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma per_k_main (m k : ℕ) (hk1 : 1 ≤ k) (h2k : 2 * k ≤ m + 1) :
  ((m + 4 : ℕ) : ℚ) * t (m + 2) k - ((2 * m + 5 : ℕ) : ℚ) * t (m + 1) k
    - ((3 * (m + 1) : ℕ) : ℚ) * t m k
    = H (m + 1) (k + 1) - H (m + 1) k := by
  have e1 := t_succ_ratio m k h2k
  have e2 := t_pred_m_ratio m k h2k
  have e3 := t_pred_ratio m k hk1 h2k
  rw [H_succ, H_pred (m + 1) k hk1]
  rw [e1, e2, e3]
  have hk1c : ((((k - 1 : ℕ))) : ℚ) = (k : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    simp
  have hm1c : ((((m + 1 - 2 * k : ℕ))) : ℚ) = (m : ℚ) + 1 - 2 * (k : ℚ) := by
    have h : 2 * k ≤ m + 1 := h2k
    rw [Nat.cast_sub h]
    push_cast
    ring
  have hm2c : ((((m + 2 - 2 * k : ℕ))) : ℚ) = (m : ℚ) + 2 - 2 * (k : ℚ) := by
    have h : 2 * k ≤ m + 2 := by omega
    rw [Nat.cast_sub h]
    push_cast
    ring
  have hm3c : ((((m + 3 - 2 * k : ℕ))) : ℚ) = (m : ℚ) + 3 - 2 * (k : ℚ) := by
    have h : 2 * k ≤ m + 3 := by omega
    rw [Nat.cast_sub h]
    push_cast
    ring
  rw [hk1c, hm1c, hm2c, hm3c]
  push_cast
  have hA : (m : ℚ) + 2 - 2 * (k : ℚ) ≠ 0 := by
    have hpos : (0 : ℚ) < (m : ℚ) + 2 - 2 * (k : ℚ) := by
      have hnat : 0 < m + 2 - 2 * k := by omega
      have hc : (0 : ℚ) < ((((m + 2 - 2 * k : ℕ))) : ℚ) := by exact_mod_cast hnat
      rwa [hm2c] at hc
    exact ne_of_gt hpos
  have hB : (m : ℚ) + 1 ≠ 0 := by positivity
  have hC : (m : ℚ) + 3 - 2 * (k : ℚ) ≠ 0 := by
    have hpos : (0 : ℚ) < (m : ℚ) + 3 - 2 * (k : ℚ) := by
      have hnat : 0 < m + 3 - 2 * k := by omega
      have hc : (0 : ℚ) < ((((m + 3 - 2 * k : ℕ))) : ℚ) := by exact_mod_cast hnat
      rwa [hm3c] at hc
    exact ne_of_gt hpos
  field_simp
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[per_k_mid](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma per_k_mid (m k : ℕ) (h : 2 * k = m + 2) :
  ((m + 4 : ℕ) : ℚ) * t (m + 2) k - ((2 * m + 5 : ℕ) : ℚ) * t (m + 1) k
    - ((3 * (m + 1) : ℕ) : ℚ) * t m k
    = H (m + 1) (k + 1) - H (m + 1) k := by
  have hk1 : 1 ≤ k := by omega
  have hC0 : Nat.choose (m + 1) (2 * k) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  have hC0m : Nat.choose m (2 * k) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  have hC1 : Nat.choose (m + 2) (2 * k) = 1 := by
    have : 2 * k = m + 2 := h
    rw [this]
    exact Nat.choose_self _
  have h2km : 2 * (k - 1) = m := by omega
  have hCm1 : Nat.choose (m + 1) (2 * (k - 1)) = m + 1 := by
    rw [h2km]
    exact Nat.choose_succ_self_right m
  have ht1 : t (m + 1) k = 0 := by unfold t; rw [hC0]; simp
  have htm : t m k = 0 := by unfold t; rw [hC0m]; simp
  rw [ht1, htm]
  simp only [mul_zero, sub_zero]
  have hH1 : H (m + 1) (k + 1) = 0 := by
    unfold H
    simp [ht1]
  rw [hH1, zero_sub]
  rw [H_pred (m + 1) k hk1]
  have htm2 : t (m + 2) k = ((catalan k : ℕ) : ℚ) := by
    unfold t; rw [hC1]; simp
  have htpred : t (m + 1) (k - 1) = ((catalan (k - 1) : ℕ) : ℚ) * (((m + 1 : ℕ)) : ℚ) := by
    unfold t; rw [hCm1]
  rw [htm2, htpred]
  have hcat := catalan_succ_Q (k - 1)
  have hk_eq : (k - 1) + 1 = k := by omega
  rw [hk_eq] at hcat
  have hk1eq : (k - 1) + 2 = k + 1 := by omega
  have h2k1 : 2 * (k - 1) + 1 = 2 * k - 1 := by omega
  rw [hk1eq, h2k1] at hcat
  have hk1c : ((((k - 1 : ℕ))) : ℚ) = (k : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    simp
  have hm_rel : (m : ℚ) = 2 * (k : ℚ) - 2 := by
    have hcast : ((2 * k : ℕ) : ℚ) = (((m + 2 : ℕ)) : ℚ) := by rw [h]
    push_cast at hcast
    linarith [hcast]
  rw [hk1c]
  rw [hcat]
  have hneD : ((((k + 1 : ℕ))) : ℚ) ≠ 0 := by positivity
  have hne2k : (((2 * k - 1 : ℕ)) : ℚ) ≠ 0 := by
    have : 0 < 2 * k - 1 := by omega
    positivity
  have h2kcast : (((2 * k - 1 : ℕ)) : ℚ) = 2 * (k : ℚ) - 1 := by
    have : 1 ≤ 2 * k := by omega
    rw [Nat.cast_sub this]
    push_cast
    ring
  rw [h2kcast]
  push_cast
  field_simp
  rw [hm_rel]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[per_k_big](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma per_k_big (m k : ℕ) (h : m + 3 ≤ 2 * k) :
  ((m + 4 : ℕ) : ℚ) * t (m + 2) k - ((2 * m + 5 : ℕ) : ℚ) * t (m + 1) k
    - ((3 * (m + 1) : ℕ) : ℚ) * t m k
    = H (m + 1) (k + 1) - H (m + 1) k := by
  have hk1 : 1 ≤ k := by omega
  have h1 : m + 2 < 2 * k := by omega
  have h2 : m + 1 < 2 * k := by omega
  have h3 : m < 2 * k := by omega
  have ht2 : t (m + 2) k = 0 := by
    unfold t
    have hz : Nat.choose (m + 2) (2 * k) = 0 := Nat.choose_eq_zero_of_lt h1
    rw [hz]; simp
  have ht1 : t (m + 1) k = 0 := by
    unfold t
    have hz : Nat.choose (m + 1) (2 * k) = 0 := Nat.choose_eq_zero_of_lt h2
    rw [hz]; simp
  have htm : t m k = 0 := by
    unfold t
    have hz : Nat.choose m (2 * k) = 0 := Nat.choose_eq_zero_of_lt h3
    rw [hz]; simp
  rw [ht2, ht1, htm]
  simp only [mul_zero, sub_zero]
  have hH1 : H (m + 1) (k + 1) = 0 := by
    rw [H_succ]
    rw [ht1]
    simp
  rw [hH1, zero_sub]
  rw [H_pred (m + 1) k hk1]
  obtain heq | hlt := eq_or_lt_of_le h
  · have hk1c : ((((k - 1 : ℕ))) : ℚ) = (k : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    simp
    have hm_rel : (m : ℚ) + 3 - 2 * (k : ℚ) = 0 := by
      have hcast : ((2 * k : ℕ) : ℚ) = (((m + 3 : ℕ)) : ℚ) := by
        have : 2 * k = m + 3 := by omega
        rw [this]
      push_cast at hcast
      linarith [hcast]
    rw [hk1c]
    have hcoeff : (((m + 1 : ℕ)) : ℚ) - 2 * ((k : ℚ) - 1) = 0 := by
      push_cast
      linarith [hm_rel]
    rw [hcoeff]
    simp
  · have h4 : m + 1 < 2 * (k - 1) := by omega
    have htz : t (m + 1) (k - 1) = 0 := by
      unfold t
      have hz : Nat.choose (m + 1) (2 * (k - 1)) = 0 := Nat.choose_eq_zero_of_lt h4
      rw [hz]; simp
    rw [htz]
    simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[per_k](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma per_k (m k : ℕ) :
  ((m + 4 : ℕ) : ℚ) * t (m + 2) k - ((2 * m + 5 : ℕ) : ℚ) * t (m + 1) k
    - ((3 * (m + 1) : ℕ) : ℚ) * t m k
    = H (m + 1) (k + 1) - H (m + 1) k := by
  obtain rfl | hk0 := eq_or_ne k 0
  · exact per_k_zero m
  · have hk1 : 1 ≤ k := by omega
    by_cases h2k : 2 * k ≤ m + 1
    · exact per_k_main m k hk1 h2k
    · have hge : m + 2 ≤ 2 * k := by omega
      obtain heq | hlt := eq_or_lt_of_le hge
      · have hmid : 2 * k = m + 2 := by omega
        exact per_k_mid m k hmid
      · have hbig : m + 3 ≤ 2 * k := by omega
        exact per_k_big m k hbig

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mot_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma mot_recurrence (m : ℕ) :
  ((m + 4 : ℕ) : ℚ) * (Mot (m + 2) : ℚ)
    = ((2 * m + 5 : ℕ) : ℚ) * (Mot (m + 1) : ℚ)
      + ((3 * (m + 1) : ℕ) : ℚ) * (Mot m : ℚ) := by
  have hm0 : m / 2 + 1 ≤ m + 3 := by omega
  have hm1 : (m + 1) / 2 + 1 ≤ m + 3 := by omega
  have hm2 : (m + 2) / 2 + 1 ≤ m + 3 := by omega
  have e0 := Mot_extend m m hm0
  have e1 := Mot_extend m (m + 1) hm1
  have e2 := Mot_extend m (m + 2) hm2
  have hsum : (∑ k ∈ Finset.range (m + 3),
    (((m + 4 : ℕ) : ℚ) * t (m + 2) k - ((2 * m + 5 : ℕ) : ℚ) * t (m + 1) k
      - ((3 * (m + 1) : ℕ) : ℚ) * t m k))
    = ∑ k ∈ Finset.range (m + 3), (H (m + 1) (k + 1) - H (m + 1) k) := by
    apply Finset.sum_congr rfl
    intro k _
    exact per_k m k
  have hLHS : (∑ k ∈ Finset.range (m + 3),
    (((m + 4 : ℕ) : ℚ) * t (m + 2) k - ((2 * m + 5 : ℕ) : ℚ) * t (m + 1) k
      - ((3 * (m + 1) : ℕ) : ℚ) * t m k))
    = ((m + 4 : ℕ) : ℚ) * (∑ k ∈ Finset.range (m + 3), t (m + 2) k)
      - ((2 * m + 5 : ℕ) : ℚ) * (∑ k ∈ Finset.range (m + 3), t (m + 1) k)
      - ((3 * (m + 1) : ℕ) : ℚ) * (∑ k ∈ Finset.range (m + 3), t m k) := by
    simp [Finset.mul_sum, Finset.sum_sub_distrib]
  have hRHS : (∑ k ∈ Finset.range (m + 3), (H (m + 1) (k + 1) - H (m + 1) k))
    = H (m + 1) (m + 3) - H (m + 1) 0 := Finset.sum_range_sub (H (m + 1)) (m + 3)
  have hHtop : H (m + 1) (m + 3) = 0 := by
    have : m + 3 = (m + 2) + 1 := by omega
    rw [this, H_succ]
    have htz : t (m + 1) (m + 2) = 0 := t_eq_zero_of_lt (by omega)
    rw [htz]
    simp
  have hHbot : H (m + 1) 0 = 0 := rfl
  rw [hLHS, hRHS, hHtop, hHbot, sub_zero] at hsum
  rw [← e0, ← e1, ← e2] at hsum
  linarith [hsum]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Mot_val0](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma Mot_val0 : Mot 0 = 1 := by
decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Mot_val1](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma Mot_val1 : Mot 1 = 1 := by
decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Mot_val2](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma Mot_val2 : Mot 2 = 2 := by
decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Mot_val3](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma Mot_val3 : Mot 3 = 4 := by
decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Mot_val4](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma Mot_val4 : Mot 4 = 9 := by
decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[rat_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma rat_pos (n : ℕ) : 0 < rat n := by
  unfold rat
  apply div_pos
  · exact_mod_cast Mot_pos (n + 1)
  · exact_mod_cast Mot_pos n

end MetaMathlibExt

namespace MetaMathlibExt

/--
[rat_succ_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma rat_succ_eq (m : ℕ) :
  rat (m + 1) = ((2 * (m + 1) + 3 : ℕ) : ℚ) / ((m + 1 + 3 : ℕ) : ℚ)
    + ((((3 * (m + 1) : ℕ)) : ℚ) / ((m + 1 + 3 : ℕ) : ℚ)) / rat m := by
  unfold rat
  have h1 : ((Mot (m + 1) : ℚ)) ≠ 0 := by exact_mod_cast ne_of_gt (Mot_pos (m + 1))
  have h2 : ((Mot m : ℚ)) ≠ 0 := by exact_mod_cast ne_of_gt (Mot_pos m)
  have hrec := mot_recurrence m
  field_simp
  linear_combination hrec

end MetaMathlibExt

namespace MetaMathlibExt

/--
[LB_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma LB_pos (n : ℕ) : 0 < LB n := by
  unfold LB
  apply div_pos <;> positivity

end MetaMathlibExt

namespace MetaMathlibExt

/--
[UB_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma UB_pos (n : ℕ) : 0 < UB n := by
  unfold UB
  apply div_pos <;> positivity

end MetaMathlibExt

namespace MetaMathlibExt

/--
[abL_eq_U](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma abL_eq_U (n : ℕ) (hn : 3 ≤ n) :
  ((2 * n + 3 : ℕ) : ℚ) / ((n + 3 : ℕ) : ℚ)
    + ((((3 * n : ℕ)) : ℚ) / ((n + 3 : ℕ) : ℚ)) / LB (n - 1)
    = UB n := by
  unfold LB UB
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have e : m + 3 - 1 = m + 2 := by omega
  rw [e]
  push_cast
  field_simp
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[abU_ge_L](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma abU_ge_L (n : ℕ) (hn : 3 ≤ n) :
  LB n ≤ ((2 * n + 3 : ℕ) : ℚ) / ((n + 3 : ℕ) : ℚ)
    + ((((3 * n : ℕ)) : ℚ) / ((n + 3 : ℕ) : ℚ)) / UB (n - 1) := by
  unfold LB UB
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have e : m + 3 - 1 = m + 2 := by omega
  rw [e]
  push_cast
  field_simp
  nlinarith [sq_nonneg (m : ℚ)]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[bounds](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma bounds (n : ℕ) (hn : 2 ≤ n) : LB n ≤ rat n ∧ rat n ≤ UB n := by
  induction n, hn using Nat.le_induction with
  | base =>
    unfold rat LB UB
    rw [Mot_val3, Mot_val2]
    norm_num
  | succ n hn ih =>
    obtain ⟨hlo, hhi⟩ := ih
    have h3 : 3 ≤ n + 1 := by omega
    have hratpos := rat_pos n
    have hLBpos := LB_pos n
    have hUBpos := UB_pos n
    have hlow : ((2 * (n+1) + 3 : ℕ) : ℚ) / ((n+1 + 3 : ℕ) : ℚ)
      + ((((3 * (n+1) : ℕ)) : ℚ) / ((n+1 + 3 : ℕ) : ℚ)) / UB n
      ≤ rat (n + 1) := by
      rw [rat_succ_eq n]
      gcongr
    have hhigh : rat (n + 1)
      ≤ ((2 * (n+1) + 3 : ℕ) : ℚ) / ((n+1 + 3 : ℕ) : ℚ)
      + ((((3 * (n+1) : ℕ)) : ℚ) / ((n+1 + 3 : ℕ) : ℚ)) / LB n := by
      rw [rat_succ_eq n]
      gcongr
    have e : n + 1 - 1 = n := by omega
    have hU : ((2 * (n+1) + 3 : ℕ) : ℚ) / ((n+1 + 3 : ℕ) : ℚ)
      + ((((3 * (n+1) : ℕ)) : ℚ) / ((n+1 + 3 : ℕ) : ℚ)) / LB ((n+1) - 1)
      = UB (n+1) := abL_eq_U (n+1) h3
    rw [e] at hU
    have hL := abU_ge_L (n+1) h3
    rw [e] at hL
    constructor
    · calc LB (n+1) ≤ _ := hL
      _ ≤ rat (n+1) := hlow
    · calc rat (n+1) ≤ _ := hhigh
      _ = UB (n+1) := hU

end MetaMathlibExt

namespace MetaMathlibExt

/--
[gap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma gap (n : ℕ) (hn : 3 ≤ n) : UB (n - 1) < LB n := by
  unfold LB UB
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have e : m + 3 - 1 = m + 2 := by omega
  rw [e]
  push_cast
  field_simp
  nlinarith [sq_nonneg (m : ℚ)]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[LB_ge_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma LB_ge_two (n : ℕ) (hn : 2 ≤ n) : 2 ≤ LB n := by
  unfold LB
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  push_cast
  field_simp
  nlinarith

end MetaMathlibExt

namespace MetaMathlibExt

/--
[rat_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma rat_one : rat 1 = 2 := by
  have h : (1 : ℕ) + 1 = 2 := rfl
  unfold rat
  rw [h, Mot_val2, Mot_val1]
  norm_num

end MetaMathlibExt

namespace MetaMathlibExt

/--
[rat_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma rat_two : rat 2 = 2 := by
  have h : (2 : ℕ) + 1 = 3 := rfl
  unfold rat
  rw [h]
  have a : Mot 3 = 4 := by decide
  have b : Mot 2 = 2 := by decide
  rw [a, b]
  norm_num

end MetaMathlibExt

namespace MetaMathlibExt

/--
[rat_mono_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma rat_mono_succ (m : ℕ) (hm : 1 ≤ m) : rat m ≤ rat (m + 1) := by
  obtain rfl | hm2 := eq_or_lt_of_le hm
  · rw [rat_one, rat_two]
  · have hm2' : 2 ≤ m := by omega
    have h3 : 3 ≤ m + 1 := by omega
    obtain ⟨_, hhi1⟩ := bounds m hm2'
    obtain ⟨hlo2, _⟩ := bounds (m + 1) (by omega)
    have e : m + 1 - 1 = m := by omega
    have hg := gap (m + 1) h3
    rw [e] at hg
    apply le_of_lt
    calc rat m < LB (m + 1) := lt_of_le_of_lt hhi1 hg
      _ ≤ rat (m + 1) := hlo2

end MetaMathlibExt

namespace MetaMathlibExt

/--
[log_convex](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma log_convex (m : ℕ) (hm : 1 ≤ m) :
  ((Mot (m + 1) : ℚ)) ^ 2 ≤ (Mot m : ℚ) * (Mot (m + 2) : ℚ) := by
  have hmono := rat_mono_succ m hm
  unfold rat at hmono
  have h1 : (0 : ℚ) < (Mot m : ℚ) := by exact_mod_cast Mot_pos m
  have h2 : (0 : ℚ) < (Mot (m + 1) : ℚ) := by exact_mod_cast Mot_pos (m + 1)
  rw [div_le_div_iff₀ h1 h2] at hmono
  calc ((Mot (m + 1) : ℚ)) ^ 2
    = (Mot (m + 1) : ℚ) * (Mot (m + 1) : ℚ) := by ring
    _ ≤ (Mot (m + 2) : ℚ) * (Mot m : ℚ) := hmono
    _ = (Mot m : ℚ) * (Mot (m + 2) : ℚ) := by ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[diff_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma diff_pos (m : ℕ) (hm : 1 ≤ m) :
  (0 : ℚ) < (Mot (m + 2) : ℚ) - (Mot (m + 1) : ℚ) := by
  have h2 : 2 ≤ m + 1 := by omega
  have hLB := LB_ge_two (m + 1) h2
  obtain ⟨hlo, _⟩ := bounds (m + 1) h2
  have h2le : (2 : ℚ) ≤ rat (m + 1) := le_trans hLB hlo
  unfold rat at h2le
  have hMpos : (0 : ℚ) < (Mot (m + 1) : ℚ) := by exact_mod_cast Mot_pos (m + 1)
  rw [le_div_iff₀ hMpos] at h2le
  nlinarith [hMpos, h2le, Mot_pos (m + 1)]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[aigner_motzkin_ratio_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
lemma aigner_motzkin_ratio_inequality
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  let M : ℕ → ℕ := by
-- proof
  intro M
  have hM : ∀ r, M r = Mot r := fun r => rfl
  simp only [hM]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have e1 : m + 1 - 1 = m := by omega
  have e2 : m + 1 + 1 = m + 2 := by omega
  rw [e1, e2]
  obtain h0 | hm := eq_or_lt_of_le hn
  · have hm0 : m = 0 := by omega
    subst hm0
    rw [Mot_val0, Mot_val1, Mot_val2]
    norm_num
  · have hm' : 1 ≤ m := by omega
    have hlog := log_convex m hm'
    have hdiff := diff_pos m hm'
    have hMpos2 : (0 : ℚ) < (Mot (m + 2) : ℚ) := by exact_mod_cast Mot_pos (m + 2)
    rw [div_le_div_iff₀ hdiff hMpos2]
    linear_combination hlog
end



-- created on 2026-10-20
-- updated on 2026-10-23
