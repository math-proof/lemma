import Mathlib
import sympy.Basic
import Def.Combinatorics.DixonSummation.Part5
open MetaMathlibExt


namespace MetaMathlibExt

/--
[invFact_shift](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean)
-/
@[path]
lemma invFact_shift
  {n : ℤ} :
-- imply
  invFact n = (n + 1) * invFact (n + 1) := by
-- proof
  by_cases hn : n < 0
  · by_cases hn1 : n = -1
    · subst n
      norm_num [invFact]
    · have hn' : n + 1 < 0 := by omega
      simp [invFact, not_le_of_gt hn, not_le_of_gt hn']
  · have hn' : 0 ≤ n := by omega
    have hn1 : 0 ≤ n + 1 := by omega
    have habs : (n + 1).natAbs = n.natAbs + 1 := by omega
    have hcast : (0 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn'
    simp [invFact, hn', hn1, habs, Nat.factorial_succ]
    field_simp
    rw [abs_of_nonneg hcast]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[dixon_sign](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean)
-/
@[path]
private lemma dixon_sign (k : ℤ) : (-1 : ℚ) ^ k.natAbs = (-1 : ℚ) ^ k := by
  obtain he | ho := Int.even_or_odd k
  · have he' : Even k.natAbs := he.natAbs
    rw [he'.neg_one_pow, he.neg_one_zpow]
  · have ho' : Odd k.natAbs := ho.natAbs
    rw [ho'.neg_one_pow, ho.neg_one_zpow]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[dixon_intBinom_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean)
-/
@[path]
private lemma dixon_intBinom_two (a k : ℤ) :
  intBinom (2 * a) (a + k) =
    extFact (2 * a) * invFact (a + k) * invFact (a - k) := by
  unfold intBinom
  rw [show 2 * a - (a + k) = a - k by ring]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[dixon_summand_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean)
-/
@[path]
private lemma dixon_summand_eq (a b c k : ℤ) :
  dixonSummand a b c k =
    extFact (2 * a) * extFact (2 * b) * extFact (2 * c) * dixon_kernel a b c k := by
  unfold dixonSummand
  rw [dixon_sign, dixon_intBinom_two, dixon_intBinom_two, dixon_intBinom_two]
  unfold dixon_kernel
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[dixon_kernel_eq_zero_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean)
-/
@[path]
private lemma dixon_kernel_eq_zero_of_not_mem (a b c k : ℤ)
  (hk : k ∉ Finset.Icc (-a) a) : dixon_kernel a b c k = 0 := by
  simp only [Finset.mem_Icc, not_and_or, not_le] at hk
  obtain hk | hk := hk
  · rw [dixon_kernel, invFact_of_neg (show a + k < 0 by omega)]
    ring
  · rw [dixon_kernel, invFact_of_neg (show a - k < 0 by omega)]
    ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[dixon_le_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean)
-/
@[path]
private lemma dixon_le_bound (a b c : ℤ) : a ≤ dixonBound a b c := by
  unfold dixonBound
  exact (le_abs_self a).trans (le_max_left _ _)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[dixon_sum_window](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean)
-/
@[path]
private lemma dixon_sum_window (a b c : ℤ) :
  (∑ k ∈ Finset.Icc (-(dixonBound a b c)) (dixonBound a b c),
    dixon_kernel a b c k) =
    ∑ k ∈ Finset.Icc (-a) a, dixon_kernel a b c k := by
  symm
  apply Finset.sum_subset
  · apply Finset.Icc_subset_Icc
    · have h := dixon_le_bound a b c
      omega
    · exact dixon_le_bound a b c
  · intro k _ hk
    exact dixon_kernel_eq_zero_of_not_mem a b c k hk

end MetaMathlibExt

namespace MetaMathlibExt

/--
[dixon_extFact_mul_invFact](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean)
-/
@[path]
private lemma dixon_extFact_mul_invFact {n : ℤ} (hn : 0 ≤ n) :
  extFact n * invFact n = 1 := by
  simp [extFact, invFact, hn]
  field_simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[dixon_invFact_mul_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean)
-/
@[path]
private lemma dixon_invFact_mul_neg (k : ℤ) (hk : k ≠ 0) :
  invFact k * invFact (-k) = 0 := by
  obtain hk | hk := lt_or_gt_of_ne hk
  · rw [invFact_of_neg hk]
    ring
  · rw [invFact_of_neg (show -k < 0 by omega)]
    ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[dixon_base](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean)
-/
@[path]
private lemma dixon_base (a b : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
  (∑ k ∈ Finset.Icc (-a) a, dixon_kernel a b 0 k) = dixon_phi a b 0 := by
  have hzero : (0 : ℤ) ∈ Finset.Icc (-a) a := by
    simp only [Finset.mem_Icc]
    omega
  rw [Finset.sum_eq_single 0]
  · have hab : 0 ≤ a + b := by omega
    have hcancel := dixon_extFact_mul_invFact hab
    unfold dixon_kernel dixon_phi
    simp only [zpow_zero, one_mul, add_zero, sub_zero]
    rw [hcancel]
    have hi0 : invFact 0 = 1 := by norm_num [invFact]
    rw [hi0]
    ring
  · intro k _ hk
    unfold dixon_kernel
    rw [zero_add, zero_sub]
    have hzero' := dixon_invFact_mul_neg k hk
    calc
      (-1 : ℚ) ^ k * invFact (a + k) * invFact (a - k) *
        invFact (b + k) * invFact (b - k) * invFact k * invFact (-k) =
        ((-1 : ℚ) ^ k * invFact (a + k) * invFact (a - k) *
          invFact (b + k) * invFact (b - k)) * (invFact k * invFact (-k)) := by ring
      _ = 0 := by rw [hzero']; ring
  · simp [hzero]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[dixon_invFact_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean)
-/
@[path]
private lemma dixon_invFact_pos {n : ℤ} (hn : 0 ≤ n) : 0 < invFact n := by
  unfold invFact
  split
  · positivity
  · contradiction

end MetaMathlibExt

namespace MetaMathlibExt

/--
[dixon_extFact_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean)
-/
@[path]
private lemma dixon_extFact_pos {n : ℤ} (hn : 0 ≤ n) : 0 < extFact n := by
  unfold extFact
  split
  · positivity
  · contradiction

end MetaMathlibExt

namespace MetaMathlibExt

/--
[dixon_phi_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean)
-/
@[path]
private lemma dixon_phi_pos (a b c : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
  0 < dixon_phi a b c := by
  have h₀ := dixon_extFact_pos (show 0 ≤ a + b + c by omega)
  have h₁ := dixon_invFact_pos (show 0 ≤ a + b by omega)
  have h₂ := dixon_invFact_pos (show 0 ≤ a + c by omega)
  have h₃ := dixon_invFact_pos (show 0 ≤ b + c by omega)
  have h₄ := dixon_invFact_pos ha
  have h₅ := dixon_invFact_pos hb
  have h₆ := dixon_invFact_pos hc
  unfold dixon_phi
  positivity

end MetaMathlibExt

namespace MetaMathlibExt

/--
[dixon_extFact_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean)
-/
@[path]
private lemma dixon_extFact_succ (n : ℤ) (hn : 0 ≤ n) :
  extFact (n + 1) = (n + 1) * extFact n := by
  have hn1 : 0 ≤ n + 1 := by omega
  have habs : (n + 1).natAbs = n.natAbs + 1 := by omega
  simp [extFact, hn, hn1, habs, Nat.factorial_succ]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[dixon_phi_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean)
-/
@[path]
private lemma dixon_phi_succ (a b c : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
  dixon_phi a b (c + 1) =
    dixon_phi a b c * (a + b + c + 1) /
      ((a + c + 1) * (b + c + 1) * (c + 1)) := by
  have h₀ : ((a + c + 1 : ℤ) : ℚ) ≠ 0 := by positivity
  have h₁ : ((b + c + 1 : ℤ) : ℚ) ≠ 0 := by positivity
  have h₂ : ((c + 1 : ℤ) : ℚ) ≠ 0 := by positivity
  unfold dixon_phi
  rw [show a + b + (c + 1) = (a + b + c) + 1 by ring,
    dixon_extFact_succ _ (by omega)]
  rw [show a + (c + 1) = a + c + 1 by ring,
    show b + (c + 1) = b + c + 1 by ring]
  rw [invFact_shift (a + c), invFact_shift (b + c), invFact_shift c]
  field_simp
  push_cast
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[dixon_invFact_pred](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean)
-/
@[path]
private lemma dixon_invFact_pred (n : ℤ) : invFact (n - 1) = n * invFact n := by
  have h := invFact_shift (n - 1)
  rw [show n - 1 + 1 = n by ring] at h
  rw [h]
  push_cast
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[dixon_sign_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean)
-/
@[path]
private lemma dixon_sign_succ (k : ℤ) : (-1 : ℚ) ^ (k + 1) = -((-1 : ℚ) ^ k) := by
  rw [zpow_add_one₀ (by norm_num) k]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[dixon_wz_pointwise](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean)
-/
@[path]
private lemma dixon_wz_pointwise (a b c k : ℤ)
  (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
  dixon_kernel a b (c + 1) k / dixon_phi a b (c + 1) -
    dixon_kernel a b c k / dixon_phi a b c =
    dixon_certificate a b c (k + 1) - dixon_certificate a b c k := by
  have hphi : dixon_phi a b c ≠ 0 := (dixon_phi_pos a b c ha hb hc).ne'
  have hs : (0 : ℚ) < (a : ℚ) + b + c + 1 := by positivity
  have hac : (0 : ℚ) < (a : ℚ) + c + 1 := by positivity
  have hbc : (0 : ℚ) < (b : ℚ) + c + 1 := by positivity
  have hc1 : (0 : ℚ) < (c : ℚ) + 1 := by positivity
  rw [dixon_phi_succ a b c ha hb hc]
  unfold dixon_kernel dixon_certificate
  rw [dixon_sign_succ]
  rw [show a + (k + 1) - 1 = a + k by ring,
    show a - (k + 1) = (a - k) - 1 by ring,
    show b + (k + 1) - 1 = b + k by ring,
    show b - (k + 1) = (b - k) - 1 by ring,
    show c + (k + 1) = c + 1 + k by ring,
    show c + 1 - (k + 1) = c - k by ring]
  rw [dixon_invFact_pred (a - k), dixon_invFact_pred (b - k),
    dixon_invFact_pred (a + k), dixon_invFact_pred (b + k),
    invFact_shift (c - k), invFact_shift (c + k)]
  rw [show c - k + 1 = c + 1 - k by ring,
    show c + k + 1 = c + 1 + k by ring]
  field_simp [hphi, hs.ne', hac.ne', hbc.ne', hc1.ne']
  push_cast
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[dixon_sum_Icc_sub](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean)
-/
@[path]
private lemma dixon_sum_Icc_sub (G : ℤ → ℚ) (a b : ℤ) (hab : a ≤ b + 1) :
  ∑ k ∈ Finset.Icc a b, (G (k + 1) - G k) = G (b + 1) - G a := by
  have key : ∀ n : ℤ, a - 1 ≤ n →
    ∑ k ∈ Finset.Icc a n, (G (k + 1) - G k) = G (n + 1) - G a := by
    intro n hn
    induction n, hn using Int.leInduction with
    | base =>
      have he : Finset.Icc a (a - 1) = (∅ : Finset ℤ) := by
        apply Finset.Icc_eq_empty
        omega
      rw [he, Finset.sum_empty, sub_add_cancel, sub_self]
    | succ n _ ih =>
      have hmem : n + 1 ∉ Finset.Icc a n := by
        simp only [Finset.mem_Icc]
        omega
      have hins : Finset.Icc a (n + 1) = insert (n + 1) (Finset.Icc a n) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hins, Finset.sum_insert hmem, ih]
      ring
  exact key b (by omega)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[dixon_certificate_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean)
-/
@[path]
private lemma dixon_certificate_top (a b c : ℤ) :
  dixon_certificate a b c (a + 1) = 0 := by
  unfold dixon_certificate
  rw [show a - (a + 1) = -1 by ring,
    invFact_of_neg (show (-1 : ℤ) < 0 by norm_num)]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[dixon_certificate_bottom](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean)
-/
@[path]
private lemma dixon_certificate_bottom (a b c : ℤ) :
  dixon_certificate a b c (-a) = 0 := by
  unfold dixon_certificate
  rw [show a + -a - 1 = -1 by ring,
    invFact_of_neg (show (-1 : ℤ) < 0 by norm_num)]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[dixon_normalized_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean)
-/
@[path]
private lemma dixon_normalized_sum (a b c : ℤ)
  (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
  (∑ k ∈ Finset.Icc (-a) a, dixon_kernel a b c k) / dixon_phi a b c = 1 := by
  induction c, hc using Int.leInduction with
  | base =>
    rw [dixon_base a b ha hb]
    exact div_self (dixon_phi_pos a b 0 ha hb (by omega)).ne'
  | succ c hc ih =>
    have hsum :
      (∑ k ∈ Finset.Icc (-a) a,
        (dixon_kernel a b (c + 1) k / dixon_phi a b (c + 1) -
          dixon_kernel a b c k / dixon_phi a b c)) = 0 := by
      calc
        _ = ∑ k ∈ Finset.Icc (-a) a,
          (dixon_certificate a b c (k + 1) - dixon_certificate a b c k) := by
            apply Finset.sum_congr rfl
            intro k _
            exact dixon_wz_pointwise a b c k ha hb hc
        _ = dixon_certificate a b c (a + 1) - dixon_certificate a b c (-a) :=
          dixon_sum_Icc_sub _ _ _ (by omega)
        _ = 0 := by rw [dixon_certificate_top, dixon_certificate_bottom, sub_self]
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div] at hsum
    exact (sub_eq_zero.mp hsum).trans ih

end MetaMathlibExt

namespace MetaMathlibExt

/--
[dixon_kernel_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean)
-/
@[path]
private lemma dixon_kernel_sum (a b c : ℤ)
  (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
  (∑ k ∈ Finset.Icc (-a) a, dixon_kernel a b c k) = dixon_phi a b c := by
  apply (div_eq_one_iff_eq (dixon_phi_pos a b c ha hb hc).ne').mp
  exact dixon_normalized_sum a b c ha hb hc

end MetaMathlibExt

namespace MetaMathlibExt

/--
[dixon_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean)
-/
@[path]
private lemma dixon_nonneg (a b c : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
  upsilon₃ a b c =
    extFact (2 * a) * extFact (2 * b) * extFact (2 * c) * dixon_phi a b c := by
  unfold upsilon₃
  simp_rw [dixon_summand_eq]
  rw [← Finset.mul_sum, dixon_sum_window, dixon_kernel_sum a b c ha hb hc]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[dixon_upsilon_of_prefactor_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean)
-/
@[path]
private lemma dixon_upsilon_of_prefactor_eq_zero (a b c : ℤ)
  (h : extFact (2 * a) * extFact (2 * b) * extFact (2 * c) = 0) :
  upsilon₃ a b c = 0 := by
  unfold upsilon₃
  apply Finset.sum_eq_zero
  intro k _
  rw [dixon_summand_eq, h, zero_mul]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[dixon_summation](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean)
-/
@[path]
lemma dixon_summation
  {a₁ a₂ a₃ : ℤ} :
-- imply
  upsilon₃ a₁ a₂ a₃ =
    extFact (2 * a₁) * extFact (2 * a₂) * extFact (2 * a₃) *
    extFact (a₁ + a₂ + a₃) * invFact (a₁ + a₂) * invFact (a₁ + a₃) *
    invFact (a₂ + a₃) * invFact a₁ * invFact a₂ * invFact a₃ := by
-- proof
  by_cases ha : a₁ < 0
  · have hzero : extFact (2 * a₁) = 0 := extFact_of_neg (by omega)
    have hpref : extFact (2 * a₁) * extFact (2 * a₂) * extFact (2 * a₃) = 0 := by
      rw [hzero]
      ring
    rw [dixon_upsilon_of_prefactor_eq_zero a₁ a₂ a₃ hpref, hzero]
    ring
  · by_cases hb : a₂ < 0
    · have hzero : extFact (2 * a₂) = 0 := extFact_of_neg (by omega)
      have hpref : extFact (2 * a₁) * extFact (2 * a₂) * extFact (2 * a₃) = 0 := by
        rw [hzero]
        ring
      rw [dixon_upsilon_of_prefactor_eq_zero a₁ a₂ a₃ hpref, hzero]
      ring
    · by_cases hc : a₃ < 0
      · have hzero : extFact (2 * a₃) = 0 := extFact_of_neg (by omega)
        have hpref : extFact (2 * a₁) * extFact (2 * a₂) * extFact (2 * a₃) = 0 := by
          rw [hzero]
          ring
        rw [dixon_upsilon_of_prefactor_eq_zero a₁ a₂ a₃ hpref, hzero]
        ring
      · have ha' : 0 ≤ a₁ := by omega
        have hb' : 0 ≤ a₂ := by omega
        have hc' : 0 ≤ a₃ := by omega
        rw [dixon_nonneg a₁ a₂ a₃ ha' hb' hc']
        unfold dixon_phi
        ring

end MetaMathlibExt

/--
[extFact_of_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean)
-/
@[path]
private lemma extFact_of_neg_eq
  {n : ℤ}
-- given
  (hn : n < 0) :
-- imply
  extFact n = 0 := by
-- proof
  apply MetaMathlibExt.extFact_of_neg hn

/--
[extFact_natCast](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean)
-/
@[path]
private lemma extFact_natCast_eq
  {n : ℕ} :
-- imply
  extFact n = n.factorial := by
-- proof
  apply MetaMathlibExt.extFact_natCast n

/--
[invFact_of_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean)
-/
@[path]
private lemma invFact_of_neg_eq
  {n : ℤ}
-- given
  (hn : n < 0) :
-- imply
  invFact n = 0 := by
-- proof
  apply MetaMathlibExt.invFact_of_neg hn

/--
[invFact_natCast](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean)
-/
@[path]
private lemma invFact_natCast_eq
  {n : ℕ} :
-- imply
  invFact n = (n.factorial : ℚ)⁻¹ := by
-- proof
  apply MetaMathlibExt.invFact_natCast n

/--
[intBinom_natCast](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean)
-/
@[path]
private lemma intBinom_natCast_eq
  {n k : ℕ}
-- given
  (hk : k ≤ n) :
-- imply
  intBinom n k = n.choose k := by
-- proof
  apply MetaMathlibExt.intBinom_natCast hk

/--
[intBinom_of_neg_right](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean)
-/
@[path]
private lemma intBinom_of_neg_right_eq
  {n k : ℤ}
-- given
  (hk : k < 0) :
-- imply
  intBinom n k = 0 := by
-- proof
  apply MetaMathlibExt.intBinom_of_neg_right hk

/--
[intBinom_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean)
-/
@[path]
private lemma intBinom_of_lt_eq
  {n k : ℤ}
-- given
  (h : n < k) :
-- imply
  intBinom n k = 0 := by
-- proof
  apply MetaMathlibExt.intBinom_of_lt h


-- created on 2026-10-20
-- updated on 2026-10-23
