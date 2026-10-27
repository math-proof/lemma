import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.BrentOsbornBinomialAbsoluteMoment
open MetaMathlibExt


namespace MetaMathlibExt

/--
[Cext_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BrentOsbornBinomialAbsoluteMoment.lean)
-/
@[path]
private lemma Cext_neg (t : ℕ) {m : ℤ} (h : m < 0) : Cext t m = 0 := by
  unfold Cext; rw [ite_eq_right (by omega)]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Cext_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BrentOsbornBinomialAbsoluteMoment.lean)
-/
@[path]
private lemma Cext_nonneg (t : ℕ) {m : ℤ} (h : 0 ≤ m) :
  Cext t m = (Nat.choose t m.toNat : ℤ) := by
unfold Cext; rw [ite_eq_left h]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Cext_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BrentOsbornBinomialAbsoluteMoment.lean)
-/
@[path]
private lemma Cext_of_lt (t : ℕ) {m : ℤ} (h : (t : ℤ) < m) : Cext t m = 0 := by
  unfold Cext; rw [ite_eq_left (by omega)]
  simp [Nat.choose_eq_zero_of_lt (show t < m.toNat by omega)]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Cext_symm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BrentOsbornBinomialAbsoluteMoment.lean)
-/
@[path]
private lemma Cext_symm (t : ℕ) (m : ℤ) : Cext t m = Cext t ((t : ℤ) - m) := by
  obtain hm | hm | hm := lt_trichotomy m 0
  · rw [Cext_neg t hm, Cext_of_lt t (by omega)]
  · subst hm; rw [Cext_nonneg t (le_refl 0), Cext_nonneg t (by simp)]; simp
  · by_cases htm : (t : ℤ) < m
    · rw [Cext_of_lt t htm, Cext_neg t (by omega)]
    · rw [Cext_nonneg t (by omega), Cext_nonneg t (by omega),
      show ((t : ℤ) - m).toNat = t - m.toNat by omega, Nat.choose_symm (by omega)]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Cext_pascal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BrentOsbornBinomialAbsoluteMoment.lean)
-/
@[path]
private lemma Cext_pascal (t : ℕ) (m : ℤ) :
  Cext (t + 1) m = Cext t (m - 1) + Cext t m := by
  obtain hm | hm | hm := lt_trichotomy m 0
  · rw [Cext_neg (t+1) hm, Cext_neg t (by omega), Cext_neg t hm]; ring
  · subst hm
    rw [Cext_nonneg (t+1) (le_refl 0), Cext_neg t (by norm_num), Cext_nonneg t (le_refl 0)]; simp
  · rw [Cext_nonneg (t+1) (by omega), Cext_nonneg t (by omega), Cext_nonneg t (by omega),
    show m.toNat = (m - 1).toNat + 1 by omega, Nat.choose_succ_succ]; push_cast; ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Cext_pascal2](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BrentOsbornBinomialAbsoluteMoment.lean)
-/
@[path]
private lemma Cext_pascal2 (t : ℕ) (m : ℤ) :
  Cext (t+2) m = Cext t (m-2) + 2*Cext t (m-1) + Cext t m := by
  rw [show t+2 = (t+1)+1 from rfl, Cext_pascal (t+1) m, Cext_pascal t (m-1), Cext_pascal t m,
    show m-1-1 = m-2 by ring]; ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[nat_moment](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BrentOsbornBinomialAbsoluteMoment.lean)
-/
@[path]
private lemma nat_moment (t j : ℕ) (ht : 2 ≤ t) (hj1 : 1 ≤ j) (hjt : j ≤ t) :
  (t - j) * j * Nat.choose t j = t * (t - 1) * Nat.choose (t - 2) (j - 1) := by
  have hid1 : t * Nat.choose (t-1) (j-1) = Nat.choose t j * j := by
    have := Nat.add_one_mul_choose_eq (t-1) (j-1)
    rwa [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)] at this
  have hid2 : (t - j) * Nat.choose (t-1) (j-1) = (t-1) * Nat.choose (t-2) (j-1) := by
    have := Nat.choose_mul_succ_eq (t-2) (j-1)
    rw [show t - 2 + 1 = t - 1 by omega, show t - 1 - (j - 1) = t - j by omega] at this
    calc (t - j) * Nat.choose (t-1) (j-1) = Nat.choose (t-1) (j-1) * (t - j) := by ring
      _ = Nat.choose (t-2) (j-1) * (t-1) := this.symm
      _ = (t-1) * Nat.choose (t-2) (j-1) := by ring
  calc (t - j) * j * Nat.choose t j = (t - j) * (Nat.choose t j * j) := by ring
    _ = (t - j) * (t * Nat.choose (t-1) (j-1)) := by rw [hid1]
    _ = t * ((t - j) * Nat.choose (t-1) (j-1)) := by ring
    _ = t * ((t-1) * Nat.choose (t-2) (j-1)) := by rw [hid2]
    _ = t * (t - 1) * Nat.choose (t - 2) (j - 1) := by ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Cext_moment](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BrentOsbornBinomialAbsoluteMoment.lean)
-/
@[path]
private lemma Cext_moment (t : ℕ) (ht : 2 ≤ t) (m : ℤ) :
  ((t:ℤ) - m) * m * Cext t m = (t:ℤ) * ((t:ℤ) - 1) * Cext (t-2) (m-1) := by
  obtain hm | hm | hm := lt_trichotomy m 0
  · rw [Cext_neg t hm, Cext_neg (t-2) (by omega)]; ring
  · subst hm; rw [Cext_neg (t-2) (by norm_num)]; ring
  · by_cases hmt : (t:ℤ) < m
    · rw [Cext_of_lt t hmt, Cext_of_lt (t-2) (by omega)]; ring
    · have hjt : m.toNat ≤ t := by omega
      rw [Cext_nonneg t (by omega), Cext_nonneg (t-2) (by omega),
        show (m-1).toNat = m.toNat - 1 by omega]
      have key := nat_moment t m.toNat ht (by omega) hjt
      have hmm : (m.toNat : ℤ) = m := Int.toNat_of_nonneg (by omega)
      rw [show ((t:ℤ) - m) = ((t - m.toNat : ℕ) : ℤ) by rw [Nat.cast_sub hjt, hmm], ← hmm,
        show ((t:ℤ) - 1) = ((t - 1 : ℕ) : ℤ) by rw [Nat.cast_sub (by omega)]; norm_num]
      exact_mod_cast key

end MetaMathlibExt

namespace MetaMathlibExt

/--
[cast2n](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BrentOsbornBinomialAbsoluteMoment.lean)
-/
@[path]
private lemma cast2n (n : ℕ) (hn : 1 ≤ n) : ((2*n-2 : ℕ) : ℤ) = 2*(n:ℤ) - 2 := by
  rw [Nat.cast_sub (by omega)]; push_cast; ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Aa_even](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BrentOsbornBinomialAbsoluteMoment.lean)
-/
@[path]
private lemma Aa_even (n : ℕ) (i : ℤ) : Aa n (-i) = Aa n i := by
  unfold Aa; rw [Cext_symm (2*n) ((n:ℤ)+(-i))]; congr 1; push_cast; ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Bb_even](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BrentOsbornBinomialAbsoluteMoment.lean)
-/
@[path]
private lemma Bb_even (n : ℕ) (hn : 1 ≤ n) (i : ℤ) : Bb n (-i) = Bb n i := by
  unfold Bb; rw [Cext_symm (2*n-2) ((n:ℤ)-1+(-i))]; congr 1; rw [cast2n n hn]; ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Bb_zero_ge](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BrentOsbornBinomialAbsoluteMoment.lean)
-/
@[path]
private lemma Bb_zero_ge (n : ℕ) (hn : 1 ≤ n) {i : ℤ} (h : (n : ℤ) ≤ i) : Bb n i = 0 := by
  unfold Bb; apply Cext_of_lt; rw [cast2n n hn]; omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[moment](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BrentOsbornBinomialAbsoluteMoment.lean)
-/
@[path]
private lemma moment (n : ℕ) (hn : 1 ≤ n) (i : ℤ) :
  ((n:ℤ)^2 - i^2) * Aa n i = 2*(n:ℤ)*(2*(n:ℤ)-1) * Bb n i := by
  unfold Aa Bb
  have h := Cext_moment (2*n) (by omega) ((n:ℤ)+i)
  rw [show ((2*n:ℕ):ℤ) = 2*(n:ℤ) by push_cast; ring] at h
  rw [show (n:ℤ)-1+i = (n:ℤ)+i-1 by ring,
    show ((n:ℤ)^2 - i^2) = (2*(n:ℤ) - ((n:ℤ)+i))*((n:ℤ)+i) by ring]
  exact h

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pascal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BrentOsbornBinomialAbsoluteMoment.lean)
-/
@[path]
private lemma pascal (n : ℕ) (hn : 1 ≤ n) (i : ℤ) :
  Aa n i = Bb n (i-1) + 2 * Bb n i + Bb n (i+1) := by
  unfold Aa
  rw [show (2*n:ℕ) = (2*n-2)+2 by omega, Cext_pascal2 (2*n-2) ((n:ℤ)+i)]
  unfold Bb
  rw [show (n:ℤ)-1+(i-1) = (n:ℤ)+i-2 by ring, show (n:ℤ)-1+i = (n:ℤ)+i-1 by ring,
    show (n:ℤ)-1+(i+1) = (n:ℤ)+i by ring]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[gg_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BrentOsbornBinomialAbsoluteMoment.lean)
-/
@[path]
private lemma gg_eq (n : ℕ) (hn : 1 ≤ n) (i j : ℤ) :
  gg n i j = KK n (i+1) (j+1) - KK n i j := by
  unfold gg KK
  simp only [add_sub_cancel_right]
  rw [pascal n hn i, pascal n hn j]; ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[KK_diag1](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BrentOsbornBinomialAbsoluteMoment.lean)
-/
@[path]
private lemma KK_diag1 (n : ℕ) (hn : 1 ≤ n) (m : ℕ) :
  KK n ((m:ℤ)+1) (-((m:ℤ)+1)) =
    Bb n ((m:ℤ)+1) * Bb n ((m:ℤ)+2) - Bb n (m:ℤ) * Bb n ((m:ℤ)+1) := by
  unfold KK
  rw [show (-((m:ℤ)+1)) - 1 = -((m:ℤ)+2) by ring, Bb_even n hn ((m:ℤ)+2),
    Bb_even n hn ((m:ℤ)+1), show ((m:ℤ)+1) - 1 = (m:ℤ) by ring]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[KK_diag2](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BrentOsbornBinomialAbsoluteMoment.lean)
-/
@[path]
private lemma KK_diag2 (n : ℕ) (hn : 1 ≤ n) (m : ℕ) :
  KK n ((m:ℤ)+1) (-(m:ℤ)) =
    Bb n ((m:ℤ)+1) * Bb n ((m:ℤ)+1) - Bb n (m:ℤ) * Bb n (m:ℤ) := by
  unfold KK
  rw [show (-(m:ℤ)) - 1 = -((m:ℤ)+1) by ring, Bb_even n hn ((m:ℤ)+1),
    Bb_even n hn (m:ℤ), show ((m:ℤ)+1) - 1 = (m:ℤ) by ring]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[sum_shift](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BrentOsbornBinomialAbsoluteMoment.lean)
-/
@[path]
private lemma sum_shift (a b : ℤ) (f : ℤ → ℤ) :
  ∑ j ∈ Finset.Icc a b, f (j+1) = ∑ j ∈ Finset.Icc (a+1) (b+1), f j := by
  rw [← Finset.map_add_right_Icc a b 1, Finset.sum_map]; rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[peel2](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BrentOsbornBinomialAbsoluteMoment.lean)
-/
@[path]
private lemma peel2 (a b : ℤ) (hab : a + 1 ≤ b) (f : ℤ → ℤ) :
  ∑ j ∈ Finset.Icc a b, f j = f a + f (a+1) + ∑ j ∈ Finset.Icc (a+2) b, f j := by
  rw [← Finset.insert_Icc_add_one_left_eq_Icc (show a ≤ b by omega),
    Finset.sum_insert (by simp)]
  rw [← Finset.insert_Icc_add_one_left_eq_Icc (show a+1 ≤ b by omega),
    Finset.sum_insert (by simp), show a+1+1 = a+2 by ring]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[tele](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BrentOsbornBinomialAbsoluteMoment.lean)
-/
@[path]
private lemma tele (φ : ℤ → ℤ) (N : ℕ) :
  ∑ m ∈ Finset.range (N+1), (φ ((m:ℤ)+1) - φ (m:ℤ)) = φ ((N:ℤ)+1) - φ 0 := by
  induction N with
  | zero => simp
  | succ K ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[row_id](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BrentOsbornBinomialAbsoluteMoment.lean)
-/
@[path]
private lemma row_id (n : ℕ) (hn : 1 ≤ n) (m : ℕ) :
  ∑ j ∈ Finset.Icc (-(m:ℤ)) (m:ℤ), gg n (m:ℤ) j
    = (Qn n (m+1) - Qn n m)
      - KK n ((m:ℤ)+1) (-((m:ℤ)+1)) - KK n ((m:ℤ)+1) (-(m:ℤ)) := by
  have hg : ∑ j ∈ Finset.Icc (-(m:ℤ)) (m:ℤ), gg n (m:ℤ) j
    = (∑ j ∈ Finset.Icc (-(m:ℤ)) (m:ℤ), KK n ((m:ℤ)+1) (j+1)) - Qn n m := by
    unfold Qn
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => gg_eq n hn (m:ℤ) j)
  have hshift : (∑ j ∈ Finset.Icc (-(m:ℤ)) (m:ℤ), KK n ((m:ℤ)+1) (j+1))
    = ∑ j ∈ Finset.Icc (-(m:ℤ)+1) ((m:ℤ)+1), KK n ((m:ℤ)+1) j :=
    sum_shift (-(m:ℤ)) (m:ℤ) (fun j => KK n ((m:ℤ)+1) j)
  have hQ : Qn n (m+1)
    = KK n ((m:ℤ)+1) (-((m:ℤ)+1)) + KK n ((m:ℤ)+1) (-(m:ℤ))
      + ∑ j ∈ Finset.Icc (-(m:ℤ)+1) ((m:ℤ)+1), KK n ((m:ℤ)+1) j := by
    unfold Qn
    rw [show (((m+1:ℕ)):ℤ) = (m:ℤ)+1 by push_cast; ring]
    rw [peel2 (-((m:ℤ)+1)) ((m:ℤ)+1) (by omega) (fun j => KK n ((m:ℤ)+1) j)]
    rw [show (-((m:ℤ)+1))+1 = -(m:ℤ) by ring]
    rw [show (-((m:ℤ)+1))+2 = -(m:ℤ)+1 by ring]
  rw [hg, hshift, hQ]; ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[tele_s](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BrentOsbornBinomialAbsoluteMoment.lean)
-/
@[path]
private lemma tele_s (n N : ℕ) :
  ∑ m ∈ Finset.range (N+1),
    (Bb n ((m:ℤ)+1) * Bb n ((m:ℤ)+2) - Bb n (m:ℤ) * Bb n ((m:ℤ)+1))
    = Bb n ((N:ℤ)+1) * Bb n ((N:ℤ)+2) - Bb n 0 * Bb n 1 := by
  induction N with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]; push_cast
    rw [show (K:ℤ)+1+1 = (K:ℤ)+2 by ring, show (K:ℤ)+1+2 = (K:ℤ)+3 by ring]; ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[tele_r](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BrentOsbornBinomialAbsoluteMoment.lean)
-/
@[path]
private lemma tele_r (n N : ℕ) :
  ∑ m ∈ Finset.range (N+1),
    (Bb n ((m:ℤ)+1) * Bb n ((m:ℤ)+1) - Bb n (m:ℤ) * Bb n (m:ℤ))
    = Bb n ((N:ℤ)+1) * Bb n ((N:ℤ)+1) - Bb n 0 * Bb n 0 := by
  induction N with
  | zero => simp
  | succ K ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Phi_eval](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BrentOsbornBinomialAbsoluteMoment.lean)
-/
@[path]
private lemma Phi_eval (n N : ℕ) (hn : 1 ≤ n) (hN : n ≤ N) :
  Phi n N = Bb n 0 * Bb n 1 + Bb n 0 ^ 2 := by
  unfold Phi
  have hrow : ∀ m ∈ Finset.range (N+1),
    (∑ j ∈ Finset.Icc (-(m:ℤ)) (m:ℤ), gg n (m:ℤ) j)
    = (Qn n (m+1) - Qn n m)
      - (Bb n ((m:ℤ)+1) * Bb n ((m:ℤ)+2) - Bb n (m:ℤ) * Bb n ((m:ℤ)+1))
      - (Bb n ((m:ℤ)+1) * Bb n ((m:ℤ)+1) - Bb n (m:ℤ) * Bb n (m:ℤ)) := by
    intro m _; rw [row_id n hn m, KK_diag1 n hn m, KK_diag2 n hn m]
  rw [Finset.sum_congr rfl hrow, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_range_sub (fun m => Qn n m) (N+1), tele_s, tele_r]
  have hb1 : Bb n ((N:ℤ)+1) = 0 := Bb_zero_ge n hn (by omega)
  have hq0 : Qn n 0 = 0 := by
    unfold Qn; simp only [Nat.cast_zero, neg_zero, Finset.Icc_self, Finset.sum_singleton]
    unfold KK; ring
  have zN : Bb n (N:ℤ) = 0 := Bb_zero_ge n hn (by exact_mod_cast hN)
  have hqN : Qn n (N+1) = 0 := by
    unfold Qn; apply Finset.sum_eq_zero; intro j _; unfold KK
    rw [show ((N+1:ℕ):ℤ) = (N:ℤ)+1 by push_cast; ring, show (N:ℤ)+1-1 = (N:ℤ) by ring,
      hb1, zN]; ring
  rw [hb1, hq0, hqN]; ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[even_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BrentOsbornBinomialAbsoluteMoment.lean)
-/
@[path]
private lemma even_sum (N : ℕ) (F : ℤ → ℤ) (hF : ∀ i, F (-i) = F i) :
  ∑ i ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), F i = F 0 + 2 * ∑ i ∈ Finset.Icc (1:ℤ) (N:ℤ), F i := by
  induction N with
  | zero => simp
  | succ K ih =>
    have e1 : Finset.Icc (-((K:ℤ)+1)) ((K:ℤ)+1)
      = insert ((K:ℤ)+1) (Finset.Icc (-((K:ℤ)+1)) (K:ℤ)) :=
      (Finset.insert_Icc_right_eq_Icc_add_one (by omega)).symm
    have e2 : Finset.Icc (-((K:ℤ)+1)) (K:ℤ)
      = insert (-((K:ℤ)+1)) (Finset.Icc (-(K:ℤ)) (K:ℤ)) := by
      have h := (Finset.insert_Icc_add_one_left_eq_Icc
        (show (-((K:ℤ)+1)) ≤ (K:ℤ) by omega)).symm
      rwa [show (-((K:ℤ)+1))+1 = -(K:ℤ) by ring] at h
    have e3 : Finset.Icc (1:ℤ) ((K:ℤ)+1) = insert ((K:ℤ)+1) (Finset.Icc 1 (K:ℤ)) :=
      (Finset.insert_Icc_right_eq_Icc_add_one (by omega)).symm
    push_cast
    rw [e1, Finset.sum_insert (by simp), e2, Finset.sum_insert (by simp), ih,
      hF ((K:ℤ)+1), e3, Finset.sum_insert (by simp)]
    ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[range_to_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BrentOsbornBinomialAbsoluteMoment.lean)
-/
@[path]
private lemma range_to_Icc (N : ℕ) (φ : ℤ → ℤ) :
  ∑ i ∈ Finset.range (N+1), φ (i:ℤ) = ∑ i ∈ Finset.Icc (0:ℤ) (N:ℤ), φ i := by
  induction N with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, show ((K+1:ℕ):ℤ) = (K:ℤ)+1 by push_cast; ring,
      ← Finset.insert_Icc_right_eq_Icc_add_one (show (0:ℤ) ≤ (K:ℤ)+1 by positivity),
      Finset.sum_insert (by simp)]
    ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[cone_moment](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BrentOsbornBinomialAbsoluteMoment.lean)
-/
@[path]
private lemma cone_moment (n : ℕ) (hn : 1 ≤ n) (i j : ℤ) :
  Aa n i * Aa n j * (i^2 - j^2) = 2*(n:ℤ)*(2*(n:ℤ)-1) * gg n i j := by
  unfold gg
  linear_combination Aa n i * moment n hn j - Aa n j * moment n hn i

end MetaMathlibExt

namespace MetaMathlibExt

/--
[coneSum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BrentOsbornBinomialAbsoluteMoment.lean)
-/
@[path]
private lemma coneSum_eq (n N : ℕ) (hn : 1 ≤ n) :
  coneSum n N = 2*(n:ℤ)*(2*(n:ℤ)-1) * Phi n N := by
  unfold coneSum Phi
  rw [range_to_Icc N (fun i => ∑ j ∈ Finset.Icc (-i) i, gg n i j)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  exact cone_moment n hn i j

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Sbox_two_Wbox](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BrentOsbornBinomialAbsoluteMoment.lean)
-/
@[path]
private lemma Sbox_two_Wbox (n N : ℕ) : Sbox n N = 2 * Wbox n N := by
  have key : ∀ i j : ℤ, Aa n i * Aa n j * |i^2 - j^2|
    = Aa n i * Aa n j * max (i^2-j^2) 0 + Aa n i * Aa n j * max (j^2-i^2) 0 := by
    intro i j
    obtain h | h := le_total (i^2) (j^2)
    · rw [abs_of_nonpos (by nlinarith), max_eq_right (by nlinarith),
      max_eq_left (by nlinarith)]; ring
    · rw [abs_of_nonneg (by nlinarith), max_eq_left (by nlinarith),
      max_eq_right (by nlinarith)]; ring
  have hW' : (∑ i ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), ∑ j ∈ Finset.Icc (-(N:ℤ)) (N:ℤ),
    Aa n i * Aa n j * max (j^2-i^2) 0) = Wbox n N := by
    unfold Wbox
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => by ring))
  unfold Sbox
  simp_rw [key, Finset.sum_add_distrib]
  rw [hW']; unfold Wbox; ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[inner_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BrentOsbornBinomialAbsoluteMoment.lean)
-/
@[path]
private lemma inner_eq (n N : ℕ) (i : ℤ) (hi0 : 0 ≤ i) (hiN : i ≤ (N : ℤ)) :
  (∑ j ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), Aa n i * Aa n j * max (i^2 - j^2) 0)
    = ∑ j ∈ Finset.Icc (-i) i, Aa n i * Aa n j * (i^2 - j^2) := by
  rw [← Finset.sum_subset
    (Finset.Icc_subset_Icc (show -(N:ℤ) ≤ -i by omega) (show i ≤ (N:ℤ) from hiN))]
  · refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.mem_Icc] at hj
    rw [max_eq_left (by nlinarith [hj.1, hj.2])]
  · intro j _ hj
    rw [Finset.mem_Icc] at hj
    have hcase : j < -i ∨ i < j := by omega
    rw [max_eq_right (by rcases hcase with h|h <;> nlinarith), mul_zero]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Wbox_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BrentOsbornBinomialAbsoluteMoment.lean)
-/
@[path]
private lemma Wbox_eq (n N : ℕ) : Wbox n N = 2 * coneSum n N := by
  have hGeven : ∀ i : ℤ,
    (∑ j ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), Aa n (-i) * Aa n j * max ((-i)^2 - j^2) 0)
    = ∑ j ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), Aa n i * Aa n j * max (i^2 - j^2) 0 := by
    intro i; refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Aa_even n i, show (-i)^2 = i^2 by ring]
  have hG0 : (∑ j ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), Aa n 0 * Aa n j * max ((0:ℤ)^2 - j^2) 0) = 0 := by
    apply Finset.sum_eq_zero; intro j _
    rw [max_eq_right (by nlinarith), mul_zero]
  unfold Wbox
  rw [even_sum N (fun i => ∑ j ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), Aa n i * Aa n j * max (i^2 - j^2) 0)
    (fun i => hGeven i)]
  simp only [hG0, zero_add]
  unfold coneSum
  rw [← Finset.insert_Icc_add_one_left_eq_Icc (show (0:ℤ) ≤ (N:ℤ) by positivity),
    Finset.sum_insert (by simp), show (0:ℤ)+1 = 1 by ring]
  have hH0 : (∑ j ∈ Finset.Icc (-(0:ℤ)) (0:ℤ), Aa n 0 * Aa n j * ((0:ℤ)^2 - j^2)) = 0 := by
    simp
  rw [hH0, zero_add]
  congr 1
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_Icc] at hi
  rw [inner_eq n N i (by omega) (by omega)]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Sbox_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BrentOsbornBinomialAbsoluteMoment.lean)
-/
@[path]
private lemma Sbox_eq (n N : ℕ) : Sbox n N = 4 * coneSum n N := by
  rw [Sbox_two_Wbox, Wbox_eq]; ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[hAk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BrentOsbornBinomialAbsoluteMoment.lean)
-/
@[path]
private lemma hAk (n k : ℕ) : (Nat.choose (2*n) k : ℤ) = Aa n ((k:ℤ)-(n:ℤ)) := by
  unfold Aa
  rw [show (n:ℤ)+((k:ℤ)-(n:ℤ)) = (k:ℤ) by ring, Cext_nonneg (2*n) (by positivity),
    Int.toNat_natCast]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[hBb0](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BrentOsbornBinomialAbsoluteMoment.lean)
-/
@[path]
private lemma hBb0 (n : ℕ) (hn : 1 ≤ n) : Bb n 0 = (Nat.choose (2*n-2) (n-1) : ℤ) := by
  unfold Bb
  rw [Cext_nonneg (2*n-2) (by omega), show ((n:ℤ)-1+0).toNat = n-1 by omega]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[hBb1](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BrentOsbornBinomialAbsoluteMoment.lean)
-/
@[path]
private lemma hBb1 (n : ℕ) (hn : 1 ≤ n) : Bb n 1 = (Nat.choose (2*n-2) n : ℤ) := by
  unfold Bb
  rw [Cext_nonneg (2*n-2) (by omega), show ((n:ℤ)-1+1).toNat = n by omega]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[shift_range](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BrentOsbornBinomialAbsoluteMoment.lean)
-/
@[path]
private lemma shift_range (n : ℕ) (ψ : ℤ → ℤ) :
  ∑ k ∈ Finset.range (2*n+1), ψ ((k:ℤ)-(n:ℤ)) = ∑ i ∈ Finset.Icc (-(n:ℤ)) (n:ℤ), ψ i := by
  rw [range_to_Icc (2*n) (fun x => ψ (x - (n:ℤ)))]
  rw [show Finset.Icc (-(n:ℤ)) (n:ℤ)
    = (Finset.Icc (0:ℤ) ((2*n:ℕ):ℤ)).map (addRightEmbedding (-(n:ℤ))) by
    rw [Finset.map_add_right_Icc]; push_cast; ring_nf]
  rw [Finset.sum_map]; rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[step0](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BrentOsbornBinomialAbsoluteMoment.lean)
-/
@[path]
private lemma step0 (n : ℕ) :
  (((∑ k : Fin (2 * n + 1), ∑ l : Fin (2 * n + 1),
    Nat.choose (2 * n) k.1 * Nat.choose (2 * n) l.1 *
      Int.natAbs (((k.1 : ℤ) - n) ^ 2 - ((l.1 : ℤ) - n) ^ 2)) : ℕ) : ℤ)
    = Sbox n n := by
  push_cast [Int.natCast_natAbs]
  rw [Fin.sum_univ_eq_sum_range (fun k => ∑ l : Fin (2*n+1),
    (Nat.choose (2*n) k : ℤ) * (Nat.choose (2*n) l.1 : ℤ)
      * |((k:ℤ)-(n:ℤ))^2 - ((l.1:ℤ)-(n:ℤ))^2|) (2*n+1)]
  rw [Finset.sum_congr rfl (fun k _ => Fin.sum_univ_eq_sum_range
    (fun l => (Nat.choose (2*n) k : ℤ) * (Nat.choose (2*n) l : ℤ)
      * |((k:ℤ)-(n:ℤ))^2 - ((l:ℤ)-(n:ℤ))^2|) (2*n+1))]
  simp_rw [hAk n]
  unfold Sbox
  rw [← shift_range n (fun i => ∑ j ∈ Finset.Icc (-(n:ℤ)) (n:ℤ), Aa n i * Aa n j * |i^2 - j^2|)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← shift_range n (fun j => Aa n ((k:ℤ)-(n:ℤ)) * Aa n j * |((k:ℤ)-(n:ℤ))^2 - j^2|)]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[brent_osborn_binomial_absolute_moment](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BrentOsbornBinomialAbsoluteMoment.lean)
-/
@[path]
lemma brent_osborn_binomial_absolute_moment
  {n : ℕ} :
-- imply
  (∑ k : Fin (2 * n + 1), ∑ l : Fin (2 * n + 1),
    Nat.choose (2 * n) k.1 * Nat.choose (2 * n) l.1 *
    Int.natAbs (((k.1 : ℤ) - n) ^ 2 - ((l.1 : ℤ) - n) ^ 2)) =
    2 * n ^ 2 * (Nat.choose (2 * n) n) ^ 2 := by
-- proof
  obtain h0 | hn := Nat.eq_zero_or_pos n
  · subst h0; simp
  · have eP1 : (Nat.choose (2*n-2) (n-1) : ℤ) + (Nat.choose (2*n-2) n : ℤ)
    = (Nat.choose (2*n-1) n : ℤ) := by
    have h := Nat.choose_succ_succ (2*n-2) (n-1)
    rw [Nat.succ_eq_add_one, Nat.succ_eq_add_one, show 2*n-2+1 = 2*n-1 by omega,
      show n-1+1 = n by omega] at h
    exact_mod_cast h.symm
    have eP2 : (Nat.choose (2*n) n : ℤ) = 2 * (Nat.choose (2*n-1) n : ℤ) := by
      have h := Nat.choose_succ_succ (2*n-1) (n-1)
      rw [Nat.succ_eq_add_one, Nat.succ_eq_add_one, show 2*n-1+1 = 2*n by omega,
        show n-1+1 = n by omega] at h
      have hs : Nat.choose (2*n-1) (n-1) = Nat.choose (2*n-1) n := by
        have := Nat.choose_symm (show n ≤ 2*n-1 by omega)
        rwa [show 2*n-1-n = n-1 by omega] at this
      rw [hs] at h
      rw [h]; push_cast; ring
    have eP3 : (2*(n:ℤ)-1) * (Nat.choose (2*n-2) (n-1) : ℤ)
      = (n:ℤ) * (Nat.choose (2*n-1) n : ℤ) := by
      have h := Nat.add_one_mul_choose_eq (2*n-2) (n-1)
      rw [show 2*n-2+1 = 2*n-1 by omega, show n-1+1 = n by omega] at h
      have hcast : ((2*n-1 : ℕ) : ℤ) = 2*(n:ℤ)-1 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
      calc (2*(n:ℤ)-1) * (Nat.choose (2*n-2) (n-1) : ℤ)
        = ((2*n-1 : ℕ) : ℤ) * (Nat.choose (2*n-2) (n-1) : ℤ) := by rw [hcast]
        _ = ((Nat.choose (2*n-1) n * n : ℕ) : ℤ) := by exact_mod_cast h
        _ = (n:ℤ) * (Nat.choose (2*n-1) n : ℤ) := by push_cast; ring
    have hS : Sbox n n = 2 * (n:ℤ)^2 * (Nat.choose (2*n) n : ℤ)^2 := by
      rw [Sbox_eq, coneSum_eq n n hn, Phi_eval n n hn (le_refl n), hBb0 n hn, hBb1 n hn]
      set c0 := (Nat.choose (2*n-2) (n-1) : ℤ)
      set c1 := (Nat.choose (2*n-2) n : ℤ)
      set d := (Nat.choose (2*n-1) n : ℤ)
      rw [eP2, show c0 * c1 + c0^2 = c0 * (c0 + c1) by ring, eP1,
        show (4:ℤ) * (2*(n:ℤ)*(2*(n:ℤ)-1) * (c0 * d)) = 8*(n:ℤ)*d*((2*(n:ℤ)-1)*c0) by ring,
        eP3]
      ring
    have hcast := step0 n
    rw [hS] at hcast
    exact_mod_cast hcast

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
