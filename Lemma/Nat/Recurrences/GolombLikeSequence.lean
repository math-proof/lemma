import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.NumberTheory.Recurrences.GolombLikeSequence.Part8
open MetaMathlibExt


namespace MetaMathlibExt

/--
[glk_l_closed](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/GolombLikeSequence.lean)
-/
@[path]
private lemma glk_l_closed
  (y z : ℤ) (k : ℕ) :
  (y - 1) * glk_l y z k = (y + z - 1) * y ^ k - z := by
  induction k with
  | zero =>
    simp only [glk_l, pow_zero, mul_one]
    ring
  | succ k ih =>
    rw [glk_l, pow_succ]
    linear_combination y * ih

end MetaMathlibExt

namespace MetaMathlibExt

/--
[glk_f_val](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/GolombLikeSequence.lean)
-/
@[path]
private lemma glk_f_val
  (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (hpar : y % 2 ≠ z % 2)
  (n : ℕ+) :
  (↑((glk_f y z hy hz hpar n).val) : ℤ) = glk_v y z hy hz n.val := by
  simp [glk_f]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[glk_seq_strict_of_strict](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/GolombLikeSequence.lean)
-/
@[path]
private lemma glk_seq_strict_of_strict (f : ℕ+ → ℕ+) (hf : StrictMono f) :
  StrictMono (glk_seq f) := by
  intro a b hab
  have hp : a.succPNat < b.succPNat := by simpa using hab
  simpa [glk_seq] using hf hp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[glk_strict_of_seq_strict](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/GolombLikeSequence.lean)
-/
@[path]
private lemma glk_strict_of_seq_strict (f : ℕ+ → ℕ+)
  (hf : StrictMono (glk_seq f)) : StrictMono f := by
  intro a b hab
  have hp : a.natPred < b.natPred := by
    have ha := a.pos
    have hb := b.pos
    change a.val - 1 < b.val - 1
    exact (Nat.sub_lt_sub_iff_right (by omega)).2 hab
  simpa [glk_seq] using hf hp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[glk_strict_interval](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/GolombLikeSequence.lean)
-/
@[path]
private lemma glk_strict_interval
  (q : ℕ → ℕ) (hq : StrictMono q) (a b m r d : ℕ)
  (ham : a ≤ m) (hmb : m ≤ b) (hab : b = a + d)
  (hqa : q a = r) (hqb : q b = r + d) :
  q m = r + (m - a) := by
  have hlo := hq.add_le_nat (m - a) a
  rw [Nat.sub_add_cancel ham, hqa] at hlo
  have hhi := hq.add_le_nat (b - m) m
  rw [Nat.sub_add_cancel hmb, hqb] at hhi
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[glk_seq_initial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/GolombLikeSequence.lean)
-/
@[path]
private lemma glk_seq_initial
  (C Y : ℕ) (q : ℕ → ℕ) (hq : StrictMono q)
  (hq0 : q 0 = C + 1)
  (hcomp : ∀ n, q (q n - 1) = Y * n + 2 * C + 1)
  (m : ℕ) (hm : m < C + 1) :
  q m = C + 1 + m := by
  have hmC : m ≤ C := by omega
  have hlo := hq.add_le_nat m 0
  simp only [Nat.add_zero, hq0] at hlo
  have hqC : q C = 2 * C + 1 := by
    simpa [hq0] using hcomp 0
  have hhi := hq.add_le_nat (C - m) m
  rw [Nat.sub_add_cancel hmC, hqC] at hhi
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[glk_unique_seq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/GolombLikeSequence.lean)
-/
@[path]
private lemma glk_unique_seq
  (C Y : ℕ) (hC : 1 ≤ C) (hY : 2 ≤ Y)
  (F q : ℕ → ℕ) (hF : StrictMono F) (hq : StrictMono q)
  (hF0 : F 0 = C + 1) (hq0 : q 0 = C + 1)
  (hFcomp : ∀ n, F (F n - 1) = Y * n + 2 * C + 1)
  (hqcomp : ∀ n, q (q n - 1) = Y * n + 2 * C + 1)
  (hFstep : ∀ n, F (n + 1) = F n + 1 ∨ F (n + 1) = F n + Y) :
  q = F := by
  funext m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm : m < C + 1
    · rw [glk_seq_initial C Y q hq hq0 hqcomp m hm,
      glk_seq_initial C Y F hF hF0 hFcomp m hm]
    · have hmC : C + 1 ≤ m := by omega
      have hex : ∃ n : ℕ, m + 1 < q (n + 1) := by
        refine ⟨m, ?_⟩
        have hgrow := hq.add_le_nat (m + 1) 0
        simp only [Nat.add_zero, hq0] at hgrow
        omega
      let n := Nat.find hex
      have hupp : m + 1 < q (n + 1) := Nat.find_spec hex
      have hlow : q n ≤ m + 1 := by
        by_cases hn : n = 0
        · rw [hn, hq0]
          omega
        · have hpred : n - 1 < Nat.find hex := by
          change n - 1 < n
          omega
          have hmin := Nat.find_min hex hpred
          change ¬m + 1 < q (n - 1 + 1) at hmin
          rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hmin
          omega
      by_cases heq : q n = m + 1
      · have hgrow := hq.add_le_nat n 0
        simp only [Nat.add_zero, hq0] at hgrow
        have hnm : n < m := by omega
        have ihn := ih n hnm
        have hgm : q m = Y * n + 2 * C + 1 := by
          have hc := hqcomp n
          have hind : q n - 1 = m := by omega
          rwa [hind] at hc
        have hFm : F m = Y * n + 2 * C + 1 := by
          have hc := hFcomp n
          have hFn : F n = m + 1 := by omega
          rw [hFn] at hc
          simpa using hc
        omega
      · have hinterior : q n < m + 1 := by omega
        have hgrow := hq.add_le_nat n 0
        simp only [Nat.add_zero, hq0] at hgrow
        have hnm : n < m := by omega
        have hn1m : n + 1 < m := by omega
        have ihn := ih n hnm
        have ihn1 := ih (n + 1) hn1m
        have hgap : q (n + 1) = q n + Y := by
          obtain hs | hs := hFstep n
          · omega
          · omega
        have hqnpos : 1 ≤ q n := by omega
        have ham : q n - 1 ≤ m := by omega
        have hmb : m ≤ q (n + 1) - 1 := by omega
        have hab : q (n + 1) - 1 = (q n - 1) + Y := by omega
        have hqa := hqcomp n
        have hqb := hqcomp (n + 1)
        simp only [Nat.mul_add, Nat.mul_one] at hqb
        have hqm := glk_strict_interval q hq (q n - 1) (q (n + 1) - 1) m
          (Y * n + 2 * C + 1) Y ham hmb hab hqa (by omega)
        have hFa : F (q n - 1) = Y * n + 2 * C + 1 := by
          rw [ihn]
          exact hFcomp n
        have hFb : F (q (n + 1) - 1) = Y * n + 2 * C + 1 + Y := by
          rw [ihn1]
          have hc := hFcomp (n + 1)
          simp only [Nat.mul_add, Nat.mul_one] at hc
          omega
        have hFm := glk_strict_interval F hF (q n - 1) (q (n + 1) - 1) m
          (Y * n + 2 * C + 1) Y ham hmb hab hFa hFb
        omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[glk_seq_zero_of_initial_int](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/GolombLikeSequence.lean)
-/
@[path]
private lemma glk_seq_zero_of_initial_int
  (y z : ℤ) (f : ℕ+ → ℕ+)
  (h : (↑((f 1).val) : ℤ) = glk_c y z + 1) :
  glk_seq f 0 = (glk_c y z).toNat + 1 := by
  have hcpos : 0 ≤ glk_c y z := by
    have hfpos := (f 1).pos
    have hfposInt : (1 : ℤ) ≤ (↑((f 1).val) : ℤ) := by exact_mod_cast hfpos
    omega
  unfold glk_seq
  rw [show (0 : ℕ).succPNat = (1 : ℕ+) by rfl]
  apply Int.ofNat_inj.mp
  push_cast
  simpa [glk_seq, Int.ofNat_toNat, max_eq_left hcpos] using h

end MetaMathlibExt

namespace MetaMathlibExt

/--
[glk_l_rat](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/GolombLikeSequence.lean)
-/
@[path]
private lemma glk_l_rat (y z : ℤ) (hy : 2 ≤ y) (k : ℕ) :
  (glk_l y z k : ℚ) =
    ((y : ℚ) + (z : ℚ) - 1) / ((y : ℚ) - 1) * (y : ℚ) ^ k -
      (z : ℚ) / ((y : ℚ) - 1) := by
  have hden : (y : ℚ) - 1 ≠ 0 := by exact_mod_cast (by omega : y - 1 ≠ 0)
  field_simp [hden]
  exact_mod_cast (by
    simpa [mul_comm] using glk_l_closed y z k :
      glk_l y z k * (y - 1) = (y + z - 1) * y ^ k - z)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[glk_offset_rat](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/GolombLikeSequence.lean)
-/
@[path]
private lemma glk_offset_rat (y j : ℤ) :
  (if j < 0 then (j : ℚ) else (y : ℚ) * (j : ℚ)) =
    ((y : ℚ) + 1) * (j : ℚ) / 2 +
      ((y : ℚ) - 1) * |(j : ℚ)| / 2 := by
  by_cases hj : j < 0
  · have hjq : (j : ℚ) < 0 := by exact_mod_cast hj
    rw [ite_eq_left hj, abs_of_neg hjq]
    ring
  · have hjq : 0 ≤ (j : ℚ) := by exact_mod_cast (by omega : 0 ≤ j)
    rw [ite_eq_right hj, abs_of_nonneg hjq]
    ring

end MetaMathlibExt

/--
[golomb_like_closed_form](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/GolombLikeSequence.lean)
-/
@[path]
private lemma golomb_like_closed_form_eq
  {y z : ℤ}
-- given
  (hy : 2 ≤ y)
  (hz : 2 - y ≤ z)
  (hpar : y % 2 ≠ z % 2) :
-- imply
  (∃! f : ℕ+ → ℕ+,
    StrictMono f ∧
    (↑((f 1).val) : ℚ) = ((y : ℚ) + (z : ℚ) + 1) / 2 ∧
    ∀ n : ℕ+,
    (↑((f (f n)).val) : ℤ) = y * (↑n.val : ℤ) + z) ∧
    ∀ f : ℕ+ → ℕ+,
    StrictMono f →
    (↑((f 1).val) : ℚ) = ((y : ℚ) + (z : ℚ) + 1) / 2 →
    (∀ n : ℕ+,
    (↑((f (f n)).val) : ℤ) = y * (↑n.val : ℤ) + z) →
    ∀ k : ℕ, ∀ j : ℤ,
    -(((y : ℚ) + (z : ℚ) - 1) / 2) * (y : ℚ) ^ k ≤ (j : ℚ) →
    (j : ℚ) < (((y : ℚ) + (z : ℚ) - 1) / 2) * (y : ℚ) ^ k →
    ∃ m : ℕ+,
    (↑m.val : ℚ) =
    (((y : ℚ) + 1) * ((y : ℚ) + (z : ℚ) - 1) /
    (2 * ((y : ℚ) - 1))) *
    (y : ℚ) ^ k -
    (z : ℚ) / ((y : ℚ) - 1) + (j : ℚ) ∧
    (↑((f m).val) : ℚ) =
    (((y : ℚ) + (z : ℚ) - 1) / ((y : ℚ) - 1)) *
    (y : ℚ) ^ (k + 1) -
    (z : ℚ) / ((y : ℚ) - 1) +
    ((y : ℚ) + 1) * (j : ℚ) / 2 +
    ((y : ℚ) - 1) * |(j : ℚ)| / 2 := by
-- proof
  apply MetaMathlibExt.golomb_like_closed_form y z hy hz hpar


-- created on 2026-10-20
-- updated on 2026-10-26
