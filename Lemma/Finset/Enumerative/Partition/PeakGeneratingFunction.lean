import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.Partition.PeakGeneratingFunction.Part9
open MetaMathlibExt


namespace MetaMathlibExt

/--
[pgf_G_constantCoeff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_G_constantCoeff (n : ℕ) :
  PowerSeries.constantCoeff (pgf_G n) = 1 := by
  induction n using Nat.twoStepInduction with
  | zero => simp [pgf_G]
  | one => simp [pgf_G]
  | more n hn hn1 =>
    rw [pgf_G]
    simp [pgf_y, pgf_x, hn, hn1, map_ofNat]
    ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_G_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_G_ne_zero (n : ℕ) : pgf_G n ≠ 0 := by
  intro h
  have hc := congrArg PowerSeries.constantCoeff h
  rw [pgf_G_constantCoeff, map_zero] at hc
  exact one_ne_zero hc

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_two_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_two_ne_zero : (2 : pgfK) ≠ 0 := by
  have hR : (2 : pgfR) ≠ 0 := by
    intro h
    have hc := congrArg PowerSeries.constantCoeff h
    rw [map_ofNat, map_zero] at hc
    norm_num at hc
  intro hK
  have hmap : algebraMap pgfR pgfK (2 : pgfR) = 0 := by
    rwa [map_ofNat]
  apply hR
  apply IsFractionRing.injective pgfR pgfK
  simpa using hmap

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_two_mul_t](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_two_mul_t : 2 * pgf_t = 2 + pgf_map pgf_y := by
  unfold pgf_t pgf_y pgf_map
  simp only [map_mul, map_pow, map_sub, map_one]
  field_simp [pgf_two_ne_zero]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_U_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_U_add_two (n : ℤ) :
  pgf_U (n + 2) = 2 * pgf_t * pgf_U (n + 1) - pgf_U n := by
  unfold pgf_U
  rw [Polynomial.Chebyshev.U_add_two]
  simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_U_diff_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_U_diff_recurrence (n : ℤ) :
  pgf_U (n + 1) - pgf_U n =
    (2 + pgf_map pgf_y) * (pgf_U n - pgf_U (n - 1)) -
      (pgf_U (n - 1) - pgf_U (n - 2)) := by
  have h1 : pgf_U (n + 1) = 2 * pgf_t * pgf_U n - pgf_U (n - 1) := by
    convert pgf_U_add_two (n - 1) using 1 <;> ring_nf
  have h0 : pgf_U n = 2 * pgf_t * pgf_U (n - 1) - pgf_U (n - 2) := by
    convert pgf_U_add_two (n - 2) using 1 <;> ring_nf
  rw [h1, h0, ← pgf_two_mul_t]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_G_eq_U_diff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_G_eq_U_diff (n : ℕ) :
  pgf_map (pgf_G n) = pgf_U ((n : ℤ) - 1) - pgf_U ((n : ℤ) - 2) := by
  induction n using Nat.twoStepInduction with
  | zero =>
    simp [pgf_G, pgf_map, pgf_U, Polynomial.Chebyshev.U_neg_one,
      Polynomial.Chebyshev.U_neg_two]
  | one =>
    simp [pgf_G, pgf_map, pgf_U, Polynomial.Chebyshev.U_zero,
      Polynomial.Chebyshev.U_neg_one]
  | more n hn hn1 =>
    rw [pgf_G]
    unfold pgf_map at hn hn1 ⊢
    rw [map_sub, map_mul, map_add, map_ofNat, hn, hn1]
    have hrec := pgf_U_diff_recurrence (n : ℤ)
    unfold pgf_map at hrec
    have e1 : ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) := by omega
    have e2 : ((n + 1 : ℕ) : ℤ) - 2 = (n : ℤ) - 1 := by omega
    have e3 : ((n + 2 : ℕ) : ℤ) - 1 = (n : ℤ) + 1 := by omega
    have e4 : ((n + 2 : ℕ) : ℤ) - 2 = (n : ℤ) := by omega
    rwa [e1, e2, e3, e4]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_A_add_B](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_A_add_B : pgf_A + pgf_B = 1 := by
  unfold pgf_A pgf_B
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_BC_sub_AD](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_BC_sub_AD : pgf_B * pgf_C - pgf_A * pgf_D = 1 := by
  unfold pgf_A pgf_B pgf_C pgf_D
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_B_add_C](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_B_add_C : pgf_B + pgf_C = 2 + pgf_y := by
  unfold pgf_B pgf_C pgf_y
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_peakTriples_eq_peak](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_peakTriples_eq_peak {n m : ℕ} (w : Fin n → Fin m) :
  pgf_peakTriples w = pgf_peak w := by
  unfold pgf_peakTriples pgf_peak
  apply Finset.card_bij (fun s _ => s.2.1)
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    obtain ⟨h01, h12, hleft, hright⟩ := hs
    unfold pgf_isPeakAt
    have hnext : s.2.1.val + 1 < n := by omega
    refine ⟨by omega, ?_⟩
    rw [dite_eq_left hnext]
    have hprev :
      (⟨s.2.1.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) s.2.1.isLt⟩ : Fin n) = s.1 :=
      Fin.ext (by
        change s.2.1.val - 1 = s.1.val
        omega)
    have hsucc : (⟨s.2.1.val + 1, hnext⟩ : Fin n) = s.2.2 :=
      Fin.ext (by
        change s.2.1.val + 1 = s.2.2.val
        omega)
    simpa [hprev, hsucc] using And.intro hleft hright
  · intro s₁ hs₁ s₂ hs₂ hmid
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs₁ hs₂
    apply Prod.ext
    · exact Fin.ext (by omega)
    · apply Prod.ext
      · exact hmid
      · exact Fin.ext (by omega)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    unfold pgf_isPeakAt at hi
    obtain ⟨hi0, hi⟩ := hi
    by_cases hnext : i.val + 1 < n
    · rw [dite_eq_left hnext] at hi
      let a : Fin n :=
        ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le i.val 1) i.isLt⟩
      let c : Fin n := ⟨i.val + 1, hnext⟩
      refine ⟨(a, i, c), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨by simp [a]; omega, by simp [c], ?_, ?_⟩
      · exact hi.1
      · exact hi.2
    · rw [dite_eq_right hnext] at hi
      exact False.elim hi

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_peak_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_peak_eq_sum {m K : ℕ} (w : Fin m → Fin K) :
  pgf_peak w = ∑ v ∈ Finset.range m, pgf_peakNat w v := by
  have hcard : pgf_peak w = ∑ i : Fin m, (if pgf_isPeakAt w i then 1 else 0) := by
    change (Finset.univ.filter _).card = _
    rw [Finset.card_filter]
  rw [hcard, ← Fin.sum_univ_eq_sum_range (pgf_peakNat w) m]
  apply Finset.sum_congr rfl
  intro i _
  unfold pgf_isPeakAt pgf_peakNat
  split_ifs with h1 h2 h3 h4 h5
  all_goals simp_all

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_peakNat_join_before](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_peakNat_join_before {n m : ℕ} (i : Fin n) (u : Fin i.val → Fin m)
  (v : Fin (n - 1 - i.val) → Fin (m + 1)) (j : ℕ) (hj : j < i.val) :
  pgf_peakNat (pgf_joinFirst ⟨i, u, v⟩) j = pgf_peakNat u j := by
  unfold pgf_peakNat pgf_joinFirst
  dsimp
  split_ifs <;> simp_all <;> omega
@[simp] private lemma pgf_suffix_index {n : ℕ} (i : Fin n) (j : ℕ)
  (hj : j < n - 1 - i.val) (h : i.val + 1 + j - i.val - 1 < n - 1 - i.val) :
  (⟨i.val + 1 + j - i.val - 1, h⟩ : Fin (n - 1 - i.val)) = ⟨j, hj⟩ := by
  apply Fin.ext
  change i.val + 1 + j - i.val - 1 = j
  omega
@[simp] private lemma pgf_suffix_prev_index {n : ℕ} (i : Fin n) (j : ℕ)
  (hj : j < n - 1 - i.val) (hj0 : 0 < j)
  (h : i.val + 1 + j - 1 - i.val - 1 < n - 1 - i.val) :
  (⟨i.val + 1 + j - 1 - i.val - 1, h⟩ : Fin (n - 1 - i.val)) =
    ⟨j - 1, by omega⟩ := by
  apply Fin.ext
  change i.val + 1 + j - 1 - i.val - 1 = j - 1
  omega
@[simp] private lemma pgf_suffix_next_index {n : ℕ} (i : Fin n) (j : ℕ)
  (hj1 : j + 1 < n - 1 - i.val)
  (h : i.val + 1 + j + 1 - i.val - 1 < n - 1 - i.val) :
  (⟨i.val + 1 + j + 1 - i.val - 1, h⟩ : Fin (n - 1 - i.val)) =
    ⟨j + 1, hj1⟩ := by
  apply Fin.ext
  change i.val + 1 + j + 1 - i.val - 1 = j + 1
  omega
set_option maxHeartbeats 1000000 in

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_peakNat_join_after](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_peakNat_join_after {n m : ℕ} (i : Fin n) (u : Fin i.val → Fin m)
  (v : Fin (n - 1 - i.val) → Fin (m + 1)) (j : ℕ)
  (hj : j < n - 1 - i.val) :
  pgf_peakNat (pgf_joinFirst ⟨i, u, v⟩) (i.val + 1 + j) = pgf_peakNat v j := by
  unfold pgf_peakNat pgf_joinFirst
  dsimp
  split_ifs <;> simp_all <;> omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_peakNat_join_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_peakNat_join_top {n m : ℕ} (i : Fin n) (u : Fin i.val → Fin m)
  (v : Fin (n - 1 - i.val) → Fin (m + 1)) :
  pgf_peakNat (pgf_joinFirst ⟨i, u, v⟩) i.val = pgf_boundary ⟨i, u, v⟩ := by
  unfold pgf_peakNat pgf_boundary pgf_joinFirst
  dsimp
  split_ifs <;> try simp_all [Fin.castSucc_lt_last] <;> try omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_peak_join](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_peak_join {n m : ℕ} (i : Fin n) (u : Fin i.val → Fin m)
  (v : Fin (n - 1 - i.val) → Fin (m + 1)) :
  pgf_peak (pgf_joinFirst ⟨i, u, v⟩) =
    pgf_peak u + pgf_boundary ⟨i, u, v⟩ + pgf_peak v := by
  rw [pgf_peak_eq_sum, pgf_peak_eq_sum, pgf_peak_eq_sum]
  rw [show Finset.range n = Finset.range (i.val + (1 + (n - 1 - i.val))) by
    congr 1
    omega]
  rw [Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [Finset.sum_range_add]
  have hprefix :
    (∑ j ∈ Finset.range i.val, pgf_peakNat (pgf_joinFirst ⟨i, u, v⟩) j) =
      ∑ j ∈ Finset.range i.val, pgf_peakNat u j := by
    apply Finset.sum_congr rfl
    intro j hj
    exact pgf_peakNat_join_before i u v j (Finset.mem_range.mp hj)
  have hsuffix :
    (∑ j ∈ Finset.range (n - 1 - i.val),
      pgf_peakNat (pgf_joinFirst ⟨i, u, v⟩) (i.val + (1 + j))) =
      ∑ j ∈ Finset.range (n - 1 - i.val), pgf_peakNat v j := by
    apply Finset.sum_congr rfl
    intro j hj
    simpa [Nat.add_assoc] using
      pgf_peakNat_join_after i u v j (Finset.mem_range.mp hj)
  rw [hprefix, hsuffix]
  simp only [Finset.sum_range_one, add_zero, pgf_peakNat_join_top]
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_peakNat_cons_last](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_peakNat_cons_last {n m : ℕ} (v : Fin n → Fin (m + 1)) (j : ℕ)
  (hj : j < n) :
  pgf_peakNat (Fin.cons (Fin.last m) v) (j + 1) = pgf_peakNat v j := by
  have hlast (a : Fin (m + 1)) : ¬Fin.last m < a := not_lt_of_ge (Fin.le_last a)
  by_cases hj0 : j = 0
  · subst j
    unfold pgf_peakNat
    simp [Fin.cons, hlast]
  have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
  have hcur (h : j + 1 < n + 1) :
    @Fin.cons n (fun _ => Fin (m + 1)) (Fin.last m) v ⟨j + 1, h⟩ = v ⟨j, hj⟩ := by
    rw [show (⟨j + 1, h⟩ : Fin (n + 1)) = Fin.succ ⟨j, hj⟩ by
      apply Fin.ext
      rfl]
    exact Fin.cons_succ _ _ _
  have hprev (hj0 : 0 < j) (h : j + 1 - 1 < n + 1) :
    @Fin.cons n (fun _ => Fin (m + 1)) (Fin.last m) v ⟨j + 1 - 1, h⟩ =
      v ⟨j - 1, by omega⟩ := by
    rw [show (⟨j + 1 - 1, h⟩ : Fin (n + 1)) = Fin.succ ⟨j - 1, by omega⟩ by
      apply Fin.ext
      simp only [Fin.val_succ]
      omega]
    exact Fin.cons_succ _ _ _
  have hnext (hj1 : j + 1 < n) (h : j + 1 + 1 < n + 1) :
    @Fin.cons n (fun _ => Fin (m + 1)) (Fin.last m) v ⟨j + 1 + 1, h⟩ =
      v ⟨j + 1, hj1⟩ := by
    rw [show (⟨j + 1 + 1, h⟩ : Fin (n + 1)) = Fin.succ ⟨j + 1, hj1⟩ by
      apply Fin.ext
      rfl]
    exact Fin.cons_succ _ _ _
  unfold pgf_peakNat
  split_ifs <;> simp_all <;> try omega
  all_goals
    have hp := hprev (by omega)
    simp_all
    omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_peak_cons_last](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_peak_cons_last {n m : ℕ} (v : Fin n → Fin (m + 1)) :
  pgf_peak (Fin.cons (Fin.last m) v) = pgf_peak v := by
  rw [pgf_peak_eq_sum, pgf_peak_eq_sum, Finset.sum_range_succ']
  have hzero : pgf_peakNat (Fin.cons (Fin.last m) v) 0 = 0 := by
    unfold pgf_peakNat
    simp
  rw [hzero, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  exact pgf_peakNat_cons_last v j (Finset.mem_range.mp hj)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_sum_start_last](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_sum_start_last (n m : ℕ) :
  (∑ w ∈ Finset.univ.filter (fun w : Fin (n + 1) → Fin (m + 1) =>
    ¬w 0 < Fin.last m), (Polynomial.X : Polynomial ℤ) ^ pgf_peak w) =
    ∑ v : Fin n → Fin (m + 1), (Polynomial.X : Polynomial ℤ) ^ pgf_peak v := by
  symm
  apply Finset.sum_bij (s := Finset.univ)
    (t := Finset.univ.filter (fun w : Fin (n + 1) → Fin (m + 1) =>
      ¬w 0 < Fin.last m)) (fun v _ => Fin.cons (Fin.last m) v)
  · intro v _
    simp
  · intro v₁ _ v₂ _ h
    funext j
    have hj := congrFun h j.succ
    simpa only [Fin.cons_succ] using hj
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    have hw0 : w 0 = Fin.last m :=
      le_antisymm (Fin.le_last _) (le_of_not_gt hw)
    refine ⟨Fin.tail w, Finset.mem_univ _, ?_⟩
    calc
      Fin.cons (Fin.last m) (Fin.tail w) = Fin.cons (w 0) (Fin.tail w) := by rw [hw0]
      _ = w := Fin.cons_self_tail w
  · intro v _
    simp only [pgf_peak_cons_last]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_L_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_L_eq (m : ℕ) :
  pgf_L m = pgf_W (m + 1) - 1 - pgf_x * pgf_W (m + 1) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
    simp [pgf_L, pgf_W, pgf_x, pgf_peak]
  | succ n =>
    simp only [pgf_L, PowerSeries.coeff_mk, Nat.zero_lt_succ, dite_true,
      map_sub, PowerSeries.coeff_one, Nat.succ_ne_zero, ite_false, sub_zero,
      pgf_x, PowerSeries.coeff_succ_X_mul, pgf_W]
    have hsplit := Finset.sum_filter_add_sum_filter_not
      (s := Finset.univ) (p := fun w : Fin (n + 1) → Fin (m + 1) =>
        w 0 < Fin.last m)
      (f := fun w => (Polynomial.X : Polynomial ℤ) ^ pgf_peak w)
    rw [pgf_sum_start_last n m] at hsplit
    rw [← hsplit]
    ring_nf
    congr 2

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_W_succ_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_W_succ_eq (m : ℕ) : pgf_W (m + 1) = pgf_W m + pgf_H m := by
  apply PowerSeries.ext
  intro n
  simp only [pgf_W, pgf_H, map_add, PowerSeries.coeff_mk]
  rw [← Equiv.sum_comp (pgf_firstTopEquiv n m)
    (fun w => (Polynomial.X : Polynomial ℤ) ^ pgf_peak w)]
  rw [Fintype.sum_sum_type]
  congr 1

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_join_weight](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_join_weight {n m : ℕ} (i : Fin n) (u : Fin i.val → Fin m)
  (v : Fin (n - 1 - i.val) → Fin (m + 1)) :
  (Polynomial.X : Polynomial ℤ) ^ pgf_peak (pgf_joinFirst ⟨i, u, v⟩) =
    Polynomial.X ^ pgf_peak u * Polynomial.X ^ pgf_peak v +
      (Polynomial.X - 1) *
        (if pgf_boundary ⟨i, u, v⟩ = 1 then
          Polynomial.X ^ pgf_peak u * Polynomial.X ^ pgf_peak v else 0) := by
  rw [pgf_peak_join, pow_add, pow_add]
  by_cases hi : 0 < i.val
  · by_cases hv : 0 < n - 1 - i.val
    · by_cases hb : v ⟨0, hv⟩ < Fin.last m
      · simp [pgf_boundary, hi, hv, hb]
        ring
      · simp [pgf_boundary, hi, hv, hb]
    · simp [pgf_boundary, hi, hv]
  · simp [pgf_boundary, hi]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_join_weight_data](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_join_weight_data {n m : ℕ} (d : pgfFirstData n m) :
  (Polynomial.X : Polynomial ℤ) ^ pgf_peak (pgf_joinFirst d) =
    Polynomial.X ^ pgf_peak d.2.1 * Polynomial.X ^ pgf_peak d.2.2 +
      (Polynomial.X - 1) *
        (if pgf_boundary d = 1 then
          Polynomial.X ^ pgf_peak d.2.1 * Polynomial.X ^ pgf_peak d.2.2 else 0) := by
  obtain ⟨i, u, v⟩ := d
  exact pgf_join_weight i u v

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_base_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_base_sum (n m : ℕ) :
  (∑ i : Fin (n + 1), ∑ uv :
    (Fin i.val → Fin m) × (Fin (n + 1 - 1 - i.val) → Fin (m + 1)),
    (Polynomial.X : Polynomial ℤ) ^ pgf_peak uv.1 * Polynomial.X ^ pgf_peak uv.2) =
    ∑ k ∈ Finset.range (n + 1),
      PowerSeries.coeff k (pgf_W m) * PowerSeries.coeff (n - k) (pgf_W (m + 1)) := by
  apply Finset.sum_bij (s := Finset.univ) (t := Finset.range (n + 1))
    (fun i _ => i.val)
  · intro i _
    exact Finset.mem_range.mpr i.isLt
  · intro i₁ _ i₂ _ h
    exact Fin.ext h
  · intro k hk
    refine ⟨⟨k, Finset.mem_range.mp hk⟩, Finset.mem_univ _, rfl⟩
  · intro i _
    simp only [pgf_W, PowerSeries.coeff_mk]
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
    rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_coeff_W_sub_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_coeff_W_sub_one (n m : ℕ) :
  PowerSeries.coeff n (pgf_W m - 1) =
    if 0 < n then
      ∑ u : Fin n → Fin m, (Polynomial.X : Polynomial ℤ) ^ pgf_peak u
    else 0 := by
  cases n with
  | zero => simp [pgf_W, pgf_peak]
  | succ n => simp [pgf_W]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_boundary_sum_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_boundary_sum_coeff (n m : ℕ) (i : Fin (n + 1)) :
  (∑ uv : (Fin i.val → Fin m) ×
    (Fin (n + 1 - 1 - i.val) → Fin (m + 1)),
    if pgf_boundary ⟨i, uv⟩ = 1 then
      (Polynomial.X : Polynomial ℤ) ^ pgf_peak uv.1 * Polynomial.X ^ pgf_peak uv.2
    else 0) =
    PowerSeries.coeff i.val (pgf_W m - 1) *
      PowerSeries.coeff (n - i.val) (pgf_L m) := by
  rw [pgf_coeff_W_sub_one]
  simp only [pgf_L, PowerSeries.coeff_mk]
  rw [Fintype.sum_prod_type]
  by_cases hi : 0 < i.val
  · by_cases hv : 0 < n - i.val
    · simp only [ite_eq_left hi, dite_eq_left hv]
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro v _
      by_cases hb : v ⟨0, hv⟩ < Fin.last m
      · simp [pgf_boundary, hi, hv, hb]
      · simp [pgf_boundary, hi, hv, hb]
    · simp only [ite_eq_left hi, dite_eq_right hv, mul_zero]
      apply Finset.sum_eq_zero
      intro u _
      apply Finset.sum_eq_zero
      intro v _
      simp [pgf_boundary, hi, hv]
  · simp only [ite_eq_right hi, zero_mul]
    apply Finset.sum_eq_zero
    intro u _
    apply Finset.sum_eq_zero
    intro v _
    simp [pgf_boundary, hi]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_boundary_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_boundary_sum (n m : ℕ) :
  (∑ i : Fin (n + 1), ∑ uv :
    (Fin i.val → Fin m) × (Fin (n + 1 - 1 - i.val) → Fin (m + 1)),
    if pgf_boundary ⟨i, uv⟩ = 1 then
      (Polynomial.X : Polynomial ℤ) ^ pgf_peak uv.1 * Polynomial.X ^ pgf_peak uv.2
    else 0) =
    ∑ k ∈ Finset.range (n + 1),
      PowerSeries.coeff k (pgf_W m - 1) * PowerSeries.coeff (n - k) (pgf_L m) := by
  apply Finset.sum_bij (s := Finset.univ) (t := Finset.range (n + 1))
    (fun i _ => i.val)
  · intro i _
    exact Finset.mem_range.mpr i.isLt
  · intro i₁ _ i₂ _ h
    exact Fin.ext h
  · intro k hk
    refine ⟨⟨k, Finset.mem_range.mp hk⟩, Finset.mem_univ _, rfl⟩
  · intro i _
    exact pgf_boundary_sum_coeff n m i

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_H_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_H_eq (m : ℕ) :
  pgf_H m = pgf_x * (pgf_W m * pgf_W (m + 1) +
    (pgf_q - 1) * ((pgf_W m - 1) * pgf_L m)) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
    simp [pgf_H, pgf_x]
  | succ n =>
    simp only [pgf_H, PowerSeries.coeff_mk, pgf_x,
      PowerSeries.coeff_succ_X_mul, map_add]
    rw [show pgf_q - 1 = PowerSeries.C ((Polynomial.X : Polynomial ℤ) - 1) by
      simp [pgf_q]]
    rw [PowerSeries.coeff_C_mul]
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rw [Fintype.sum_sigma]
    calc
      (∑ i : Fin (n + 1), ∑ uv :
        (Fin i.val → Fin m) × (Fin (n + 1 - 1 - i.val) → Fin (m + 1)),
        (Polynomial.X : Polynomial ℤ) ^ pgf_peak (pgf_joinFirst ⟨i, uv⟩)) =
          (∑ i : Fin (n + 1), ∑ uv :
            (Fin i.val → Fin m) × (Fin (n + 1 - 1 - i.val) → Fin (m + 1)),
            Polynomial.X ^ pgf_peak uv.1 * Polynomial.X ^ pgf_peak uv.2) +
          (Polynomial.X - 1) *
            (∑ i : Fin (n + 1), ∑ uv :
              (Fin i.val → Fin m) × (Fin (n + 1 - 1 - i.val) → Fin (m + 1)),
              if pgf_boundary ⟨i, uv⟩ = 1 then
                Polynomial.X ^ pgf_peak uv.1 * Polynomial.X ^ pgf_peak uv.2
              else 0) := by
        simp_rw [pgf_join_weight_data, Finset.sum_add_distrib, Finset.mul_sum]
      _ = _ := by rw [pgf_base_sum, pgf_boundary_sum]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_W_raw_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_W_raw_recurrence (m : ℕ) :
  pgf_W (m + 1) = pgf_W m +
    pgf_x * pgf_W m * pgf_W (m + 1) +
    pgf_x * (pgf_q - 1) * (pgf_W m - 1) *
      (pgf_W (m + 1) - 1 - pgf_x * pgf_W (m + 1)) := by
  calc
    pgf_W (m + 1) = pgf_W m + pgf_H m := pgf_W_succ_eq m
    _ = _ := by rw [pgf_H_eq, pgf_L_eq]; ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_W_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_W_recurrence (m : ℕ) :
  (pgf_C + pgf_D * pgf_W m) * pgf_W (m + 1) =
    pgf_A + pgf_B * pgf_W m := by
  have h := pgf_W_raw_recurrence m
  unfold pgf_A pgf_B pgf_C pgf_D at ⊢
  linear_combination h

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_W_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_W_zero : pgf_W 0 = 1 := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [pgf_W, pgf_peak]
  | succ n => simp [pgf_W]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_G_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_G_recurrence (m : ℕ) :
  pgf_G (m + 2) = (pgf_B + pgf_C) * pgf_G (m + 1) - pgf_G m := by
  rw [pgf_G, pgf_B_add_C]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_DA_sub_CB](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_DA_sub_CB : pgf_D * pgf_A - pgf_C * pgf_B = -1 := by
  have h := pgf_BC_sub_AD
  linear_combination -h

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_W_G_identity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_W_G_identity (m : ℕ) :
  pgf_W m * pgf_den m = pgf_A * pgf_G m := by
  induction m with
  | zero =>
    rw [pgf_W_zero]
    simp only [pgf_den, pgf_G, one_mul, mul_one]
    rw [← pgf_A_add_B]
    ring
  | succ m ih =>
    have hden : (pgf_C + pgf_D * pgf_W m) * pgf_den m = pgf_den (m + 1) := by
      calc
        (pgf_C + pgf_D * pgf_W m) * pgf_den m =
          pgf_C * pgf_den m + pgf_D * (pgf_W m * pgf_den m) := by ring
        _ = pgf_C * pgf_den m + pgf_D * (pgf_A * pgf_G m) := by rw [ih]
        _ =
          pgf_C * pgf_G (m + 1) +
            (pgf_D * pgf_A - pgf_C * pgf_B) * pgf_G m := by
          rw [pgf_den]
          ring
        _ = pgf_C * pgf_G (m + 1) - pgf_G m := by rw [pgf_DA_sub_CB]; ring
        _ = pgf_den (m + 1) := by
          rw [pgf_den, pgf_G_recurrence]
          ring
    have hnum : (pgf_A + pgf_B * pgf_W m) * pgf_den m =
      pgf_A * pgf_G (m + 1) := by
      rw [add_mul, mul_assoc, ih, pgf_den]
      ring
    calc
      pgf_W (m + 1) * pgf_den (m + 1) =
        pgf_W (m + 1) * ((pgf_C + pgf_D * pgf_W m) * pgf_den m) := by
        rw [hden]
      _ = ((pgf_C + pgf_D * pgf_W m) * pgf_W (m + 1)) * pgf_den m := by ring
      _ = (pgf_A + pgf_B * pgf_W m) * pgf_den m := by rw [pgf_W_recurrence]
      _ = pgf_A * pgf_G (m + 1) := hnum

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_A_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_A_ne_zero : pgf_A ≠ 0 := by
  have hcoeff : PowerSeries.coeff 1 pgf_A = (Polynomial.X : Polynomial ℤ) - 1 := by
    unfold pgf_A pgf_x
    rw [show 1 = 0 + 1 by omega, PowerSeries.coeff_succ_X_mul]
    simp [pgf_q]
  intro h
  have hc := congrArg (PowerSeries.coeff 1) h
  rw [hcoeff, map_zero] at hc
  have hp := congrArg (fun p : Polynomial ℤ => p.coeff 1) hc
  norm_num [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_one] at hp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_den_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_den_ne_zero (m : ℕ) : pgf_den m ≠ 0 := by
  intro hden
  have h := pgf_W_G_identity m
  rw [hden, mul_zero] at h
  exact (mul_ne_zero pgf_A_ne_zero (pgf_G_ne_zero m)) h.symm

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_map_G_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_map_G_ne_zero (m : ℕ) : pgf_map (pgf_G m) ≠ 0 := by
  intro h
  apply pgf_G_ne_zero m
  apply IsFractionRing.injective pgfR pgfK
  simpa [pgf_map] using h

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_map_den_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_map_den_ne_zero (m : ℕ) : pgf_map (pgf_den m) ≠ 0 := by
  intro h
  apply pgf_den_ne_zero m
  apply IsFractionRing.injective pgfR pgfK
  simpa [pgf_map] using h

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_W_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_W_ratio (m : ℕ) :
  pgf_map (pgf_W m) =
    pgf_map pgf_A /
      (pgf_map (pgf_G (m + 1)) / pgf_map (pgf_G m) - pgf_map pgf_B) := by
  have h := congrArg pgf_map (pgf_W_G_identity m)
  unfold pgf_map at h ⊢
  simp only [map_mul] at h
  unfold pgf_den at h
  simp only [map_sub, map_mul] at h
  have hg := pgf_map_G_ne_zero m
  unfold pgf_map at hg
  have hd : algebraMap pgfR pgfK (pgf_G (m + 1)) -
    algebraMap pgfR pgfK pgf_B * algebraMap pgfR pgfK (pgf_G m) ≠ 0 := by
    simpa [pgf_map, pgf_den] using pgf_map_den_ne_zero m
  have hr : algebraMap pgfR pgfK (pgf_G (m + 1)) /
    algebraMap pgfR pgfK (pgf_G m) - algebraMap pgfR pgfK pgf_B ≠ 0 := by
    intro hr
    apply hd
    calc
      algebraMap pgfR pgfK (pgf_G (m + 1)) -
        algebraMap pgfR pgfK pgf_B * algebraMap pgfR pgfK (pgf_G m) =
        (algebraMap pgfR pgfK (pgf_G (m + 1)) /
          algebraMap pgfR pgfK (pgf_G m) - algebraMap pgfR pgfK pgf_B) *
            algebraMap pgfR pgfK (pgf_G m) := by field_simp
      _ = 0 := by rw [hr, zero_mul]
  apply (eq_div_iff hr).2
  field_simp
  simpa [mul_comm] using h

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_PP_succ_eq_PH](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_PP_succ_eq_PH (k : ℕ) : pgf_PP (k + 1) = pgf_PH k := by
  apply PowerSeries.ext
  intro n
  simp only [pgf_PP, pgf_PH, PowerSeries.coeff_mk]
  rw [Finset.sum_subtype (p := fun w : Fin n → Fin (k + 1) =>
    IsSurjectiveRestrictedGrowthString w) (Finset.univ.filter
    (fun w : Fin n → Fin (k + 1) => IsSurjectiveRestrictedGrowthString w)) (by simp)
    (fun w => (Polynomial.X : Polynomial ℤ) ^ pgf_peak w)]
  rw [← Equiv.sum_comp (pgf_rgJoinEquiv n k)
    (fun w => (Polynomial.X : Polynomial ℤ) ^ pgf_peak w.val)]
  change (∑ d : {d : pgfFirstData n k // IsSurjectiveRestrictedGrowthString d.2.1},
    (Polynomial.X : Polynomial ℤ) ^ pgf_peak (pgf_joinFirst d.val)) = _
  rw [← Finset.sum_subtype (p := fun d : pgfFirstData n k =>
    IsSurjectiveRestrictedGrowthString d.2.1) (Finset.univ.filter
    (fun d : pgfFirstData n k => IsSurjectiveRestrictedGrowthString d.2.1)) (by simp)
    (fun d => (Polynomial.X : Polynomial ℤ) ^ pgf_peak (pgf_joinFirst d))]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_rg_base_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_rg_base_sum (n k : ℕ) :
  (∑ i : Fin (n + 1), ∑ uv :
    (Fin i.val → Fin k) × (Fin (n + 1 - 1 - i.val) → Fin (k + 1)),
    if IsSurjectiveRestrictedGrowthString uv.1 then
      (Polynomial.X : Polynomial ℤ) ^ pgf_peak uv.1 * Polynomial.X ^ pgf_peak uv.2
    else 0) =
    ∑ j ∈ Finset.range (n + 1),
      PowerSeries.coeff j (pgf_PP k) * PowerSeries.coeff (n - j) (pgf_W (k + 1)) := by
  apply Finset.sum_bij (s := Finset.univ) (t := Finset.range (n + 1))
    (fun i _ => i.val)
  · intro i _
    exact Finset.mem_range.mpr i.isLt
  · intro i₁ _ i₂ _ h
    exact Fin.ext h
  · intro j hj
    refine ⟨⟨j, Finset.mem_range.mp hj⟩, Finset.mem_univ _, rfl⟩
  · intro i _
    simp only [pgf_PP, pgf_W, PowerSeries.coeff_mk]
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro u _
    by_cases hu : IsSurjectiveRestrictedGrowthString u <;> simp [hu]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_rg_domain_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_rg_domain_pos {n k : ℕ} (u : Fin n → Fin (k + 1))
  (hu : IsSurjectiveRestrictedGrowthString u) : 0 < n := by
  obtain ⟨j, _⟩ := hu.1 (0 : Fin (k + 1))
  exact lt_of_le_of_lt (Nat.zero_le j.val) j.isLt

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_L_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_L_zero : pgf_L 0 = 0 := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [pgf_L]
  | succ n =>
    simp only [pgf_L, PowerSeries.coeff_mk, Nat.zero_lt_succ, dite_true]
    apply Finset.sum_eq_zero
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    have hw0 := Fin.eq_zero (w ⟨0, Nat.zero_lt_succ n⟩)
    have hlast := Fin.eq_zero (Fin.last 0)
    rw [hw0, hlast] at hw
    exact False.elim ((lt_irrefl _) hw)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_rg_boundary_sum_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_rg_boundary_sum_coeff (n k : ℕ) (i : Fin (n + 1)) :
  (∑ uv : (Fin i.val → Fin (k + 1)) ×
    (Fin (n + 1 - 1 - i.val) → Fin (k + 2)),
    if IsSurjectiveRestrictedGrowthString uv.1 then
      if pgf_boundary ⟨i, uv⟩ = 1 then
        (Polynomial.X : Polynomial ℤ) ^ pgf_peak uv.1 * Polynomial.X ^ pgf_peak uv.2
      else 0
    else 0) =
    PowerSeries.coeff i.val (pgf_PP (k + 1)) *
      PowerSeries.coeff (n - i.val) (pgf_L (k + 1)) := by
  simp only [pgf_PP, pgf_L, PowerSeries.coeff_mk]
  rw [Fintype.sum_prod_type]
  by_cases hi : 0 < i.val
  · by_cases hv : 0 < n - i.val
    · simp only [dite_eq_left hv]
      rw [Finset.sum_mul_sum]
      simp_rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro u _
      by_cases hu : IsSurjectiveRestrictedGrowthString u
      · simp only [hu, ↓reduceIte]
        apply Finset.sum_congr rfl
        intro v _
        by_cases hb : v ⟨0, hv⟩ < Fin.last (k + 1)
        · simp [pgf_boundary, hi, hv, hb]
        · simp [pgf_boundary, hi, hv, hb]
      · simp [hu]
    · simp only [dite_eq_right hv, mul_zero]
      apply Finset.sum_eq_zero
      intro u _
      apply Finset.sum_eq_zero
      intro v _
      simp [pgf_boundary, hi, hv]
  · have hPP :
    (∑ u ∈ Finset.univ.filter
      (fun u : Fin i.val → Fin (k + 1) => IsSurjectiveRestrictedGrowthString u),
      (Polynomial.X : Polynomial ℤ) ^ pgf_peak u) = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    exact False.elim (hi (pgf_rg_domain_pos u hu))
    rw [hPP, zero_mul]
    apply Finset.sum_eq_zero
    intro u _
    apply Finset.sum_eq_zero
    intro v _
    by_cases hu : IsSurjectiveRestrictedGrowthString u
    · exact False.elim (hi (pgf_rg_domain_pos u hu))
    · simp [hu]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_rg_boundary_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_rg_boundary_sum (n k : ℕ) :
  (∑ i : Fin (n + 1), ∑ uv :
    (Fin i.val → Fin (k + 1)) × (Fin (n + 1 - 1 - i.val) → Fin (k + 2)),
    if IsSurjectiveRestrictedGrowthString uv.1 then
      if pgf_boundary ⟨i, uv⟩ = 1 then
        (Polynomial.X : Polynomial ℤ) ^ pgf_peak uv.1 * Polynomial.X ^ pgf_peak uv.2
      else 0
    else 0) =
    ∑ j ∈ Finset.range (n + 1),
      PowerSeries.coeff j (pgf_PP (k + 1)) *
        PowerSeries.coeff (n - j) (pgf_L (k + 1)) := by
  apply Finset.sum_bij (s := Finset.univ) (t := Finset.range (n + 1))
    (fun i _ => i.val)
  · intro i _
    exact Finset.mem_range.mpr i.isLt
  · intro i₁ _ i₂ _ h
    exact Fin.ext h
  · intro j hj
    refine ⟨⟨j, Finset.mem_range.mp hj⟩, Finset.mem_univ _, rfl⟩
  · intro i _
    exact pgf_rg_boundary_sum_coeff n k i

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_rg_join_weight](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_rg_join_weight {n k : ℕ} (i : Fin n)
  (uv : (Fin i.val → Fin k) × (Fin (n - 1 - i.val) → Fin (k + 1))) :
  (if IsSurjectiveRestrictedGrowthString uv.1 then
    (Polynomial.X : Polynomial ℤ) ^ pgf_peak (pgf_joinFirst ⟨i, uv⟩)
  else 0) =
    (if IsSurjectiveRestrictedGrowthString uv.1 then
      Polynomial.X ^ pgf_peak uv.1 * Polynomial.X ^ pgf_peak uv.2
    else 0) +
    (Polynomial.X - 1) *
      (if IsSurjectiveRestrictedGrowthString uv.1 then
        if pgf_boundary ⟨i, uv⟩ = 1 then
          Polynomial.X ^ pgf_peak uv.1 * Polynomial.X ^ pgf_peak uv.2
        else 0
      else 0) := by
  by_cases hu : IsSurjectiveRestrictedGrowthString uv.1
  · simp only [hu, ↓reduceIte]
    exact pgf_join_weight_data ⟨i, uv⟩
  · simp [hu]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_PH_positive_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_PH_positive_recurrence (k : ℕ) :
  pgf_PH (k + 1) = pgf_x *
    (pgf_PP (k + 1) * pgf_W (k + 2) +
      (pgf_q - 1) * (pgf_PP (k + 1) * pgf_L (k + 1))) := by
  apply PowerSeries.ext
  intro s
  cases s with
  | zero => simp [pgf_PH, pgf_x]
  | succ n =>
    simp only [pgf_PH, PowerSeries.coeff_mk, pgf_x,
      PowerSeries.coeff_succ_X_mul, map_add]
    rw [Finset.sum_filter]
    rw [show pgf_q - 1 = PowerSeries.C ((Polynomial.X : Polynomial ℤ) - 1) by
      simp [pgf_q]]
    rw [PowerSeries.coeff_C_mul]
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rw [Fintype.sum_sigma]
    calc
      (∑ i : Fin (n + 1), ∑ uv :
        (Fin i.val → Fin (k + 1)) ×
          (Fin (n + 1 - 1 - i.val) → Fin (k + 2)),
        if IsSurjectiveRestrictedGrowthString uv.1 then
          (Polynomial.X : Polynomial ℤ) ^ pgf_peak (pgf_joinFirst ⟨i, uv⟩)
        else 0) =
          (∑ i : Fin (n + 1), ∑ uv :
            (Fin i.val → Fin (k + 1)) ×
              (Fin (n + 1 - 1 - i.val) → Fin (k + 2)),
            if IsSurjectiveRestrictedGrowthString uv.1 then
              Polynomial.X ^ pgf_peak uv.1 * Polynomial.X ^ pgf_peak uv.2
            else 0) +
          (Polynomial.X - 1) *
            (∑ i : Fin (n + 1), ∑ uv :
              (Fin i.val → Fin (k + 1)) ×
                (Fin (n + 1 - 1 - i.val) → Fin (k + 2)),
              if IsSurjectiveRestrictedGrowthString uv.1 then
                if pgf_boundary ⟨i, uv⟩ = 1 then
                  Polynomial.X ^ pgf_peak uv.1 * Polynomial.X ^ pgf_peak uv.2
                else 0
              else 0) := by
        simp_rw [pgf_rg_join_weight, Finset.sum_add_distrib, Finset.mul_sum]
      _ = _ := by rw [pgf_rg_base_sum, pgf_rg_boundary_sum]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_peak_fin_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_peak_fin_one {n : ℕ} (w : Fin n → Fin 1) : pgf_peak w = 0 := by
  unfold pgf_peak
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _
  have hnot (a b : Fin 1) : ¬a < b := by
    rw [Fin.eq_zero a, Fin.eq_zero b]
    exact lt_irrefl _
  simp [pgf_isPeakAt, hnot]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_PP_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_PP_one : pgf_PP 1 = pgf_x * pgf_W 1 := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
    simp only [pgf_PP, pgf_x, PowerSeries.coeff_mk]
    rw [PowerSeries.coeff_zero_X_mul]
    apply Finset.sum_eq_zero
    intro w hw
    have hsurj := (Finset.mem_filter.mp hw).2.1
    obtain ⟨j, _⟩ := hsurj (0 : Fin 1)
    exact Fin.elim0 j
  | succ n =>
    simp only [pgf_x, PowerSeries.coeff_succ_X_mul, pgf_PP, pgf_W,
      PowerSeries.coeff_mk]
    rw [Finset.filter_eq_self.mpr]
    · simp_rw [pgf_peak_fin_one]
      simp
    · intro w _
      constructor
      · intro b
        refine ⟨0, ?_⟩
        exact Fin.eq_zero (w 0) |>.trans (Fin.eq_zero b).symm
      · intro i a h
        have ha := Fin.eq_zero a
        have hwi := Fin.eq_zero (w i)
        rw [ha, hwi] at h
        omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_F_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_F_eq (j : ℕ) :
  pgf_F j = pgf_W j + (pgf_q - 1) *
    (pgf_W j - 1 - pgf_x * pgf_W j) := by
  unfold pgf_F
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_F_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_F_one : pgf_F 1 = pgf_W 1 := by
  rw [pgf_F_eq, ← pgf_L_eq 0, pgf_L_zero]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_PP_one_factor](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_PP_one_factor : pgf_PP 1 = pgf_x * pgf_F 1 := by
  rw [pgf_PP_one, pgf_F_one]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_PP_succ_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_PP_succ_recurrence (k : ℕ) :
  pgf_PP (k + 2) = pgf_x * pgf_PP (k + 1) * pgf_F (k + 2) := by
  calc
    pgf_PP (k + 2) = pgf_PH (k + 1) := by
      simpa [Nat.add_assoc] using pgf_PP_succ_eq_PH (k + 1)
    _ = pgf_x * (pgf_PP (k + 1) * pgf_W (k + 2) +
      (pgf_q - 1) * (pgf_PP (k + 1) * pgf_L (k + 1))) :=
      pgf_PH_positive_recurrence k
    _ = pgf_x * pgf_PP (k + 1) * pgf_F (k + 2) := by
      rw [pgf_F_eq, pgf_L_eq]
      ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_PP_next](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_PP_next (k : ℕ) (hk : 1 ≤ k) :
  pgf_PP (k + 1) = pgf_x * pgf_PP k * pgf_F (k + 1) := by
  have h1 : k - 1 + 1 = k := by omega
  have h2 : k - 1 + 2 = k + 1 := by omega
  simpa only [h1, h2] using pgf_PP_succ_recurrence (k - 1)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_PP_product](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_PP_product (k : ℕ) (hk : 1 ≤ k) :
  pgf_PP k = pgf_x ^ k * ∏ j ∈ Finset.Icc 1 k, pgf_F j := by
  induction k, hk using Nat.le_induction with
  | base =>
    rw [pgf_PP_one_factor]
    simp
  | succ k hk ih =>
    rw [pgf_PP_next k hk, ih]
    rw [Finset.prod_Icc_succ_top (by omega)]
    rw [pow_succ]
    ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_r_sub_B_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_r_sub_B_ne_zero (j : ℕ) : pgf_r j - pgf_map pgf_B ≠ 0 := by
  have hg := pgf_map_G_ne_zero j
  have hd := pgf_map_den_ne_zero j
  unfold pgf_map at hg hd
  unfold pgf_den at hd
  unfold pgf_r pgf_map at ⊢
  simp only [map_sub, map_mul] at hd
  intro hr
  apply hd
  calc
    algebraMap pgfR pgfK (pgf_G (j + 1)) -
      algebraMap pgfR pgfK pgf_B * algebraMap pgfR pgfK (pgf_G j) =
      (algebraMap pgfR pgfK (pgf_G (j + 1)) /
        algebraMap pgfR pgfK (pgf_G j) - algebraMap pgfR pgfK pgf_B) *
          algebraMap pgfR pgfK (pgf_G j) := by field_simp
    _ = 0 := by rw [hr, zero_mul]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_map_F](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_map_F (j : ℕ) :
  pgf_map (pgf_F j) =
    (1 - pgf_map pgf_q) *
      (1 + pgf_map pgf_x + pgf_map pgf_x ^ 2 * (1 - pgf_map pgf_q) - pgf_r j) /
      (1 + pgf_map pgf_x * (1 - pgf_map pgf_q) - pgf_r j) := by
  have hd := pgf_r_sub_B_ne_zero j
  have hB : pgf_map pgf_B = 1 + pgf_map pgf_x * (1 - pgf_map pgf_q) := by
    unfold pgf_B pgf_map
    simp only [map_sub, map_one, map_mul]
    ring
  have hd' : 1 + pgf_map pgf_x * (1 - pgf_map pgf_q) - pgf_r j ≠ 0 := by
    rw [← hB]
    exact sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hd))
  have hW : pgf_map (pgf_W j) = pgf_map pgf_A / (pgf_r j - pgf_map pgf_B) := by
    simpa only [pgf_r] using pgf_W_ratio j
  have hA : pgf_map pgf_A = pgf_map pgf_x * (pgf_map pgf_q - 1) := by
    unfold pgf_A pgf_map
    simp only [map_mul, map_sub, map_one]
  unfold pgf_F
  change algebraMap pgfR pgfK
    (1 + pgf_x * (1 - pgf_q) * pgf_W j + pgf_q * (pgf_W j - 1)) = _
  simp only [map_add, map_mul, map_sub, map_one]
  unfold pgf_map at hW hA hB hd hd' ⊢
  rw [hW]
  rw [hA]
  field_simp [hd, hd']
  rw [hB]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_r_eq_U](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_r_eq_U (j : ℕ) :
  pgf_r j =
    (pgf_U (j : ℤ) - pgf_U ((j : ℤ) - 1)) /
      (pgf_U ((j : ℤ) - 1) - pgf_U ((j : ℤ) - 2)) := by
  unfold pgf_r
  rw [pgf_G_eq_U_diff, pgf_G_eq_U_diff]
  have h0 : ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) := by omega
  have h1 : ((j + 1 : ℕ) : ℤ) - 2 = (j : ℤ) - 1 := by omega
  rw [h0, h1]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_map_PP_closed](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_map_PP_closed (k : ℕ) (hk : 1 ≤ k) :
  pgf_map (pgf_PP k) =
    pgf_map pgf_x ^ k * (1 - pgf_map pgf_q) ^ k * ∏ j ∈ Finset.Icc 1 k,
      (1 + pgf_map pgf_x + pgf_map pgf_x ^ 2 * (1 - pgf_map pgf_q) -
        (pgf_U (j : ℤ) - pgf_U ((j : ℤ) - 1)) /
          (pgf_U ((j : ℤ) - 1) - pgf_U ((j : ℤ) - 2))) /
      (1 + pgf_map pgf_x * (1 - pgf_map pgf_q) -
        (pgf_U (j : ℤ) - pgf_U ((j : ℤ) - 1)) /
          (pgf_U ((j : ℤ) - 1) - pgf_U ((j : ℤ) - 2))) := by
  calc
    pgf_map (pgf_PP k) = pgf_map
      (pgf_x ^ k * ∏ j ∈ Finset.Icc 1 k, pgf_F j) := by rw [pgf_PP_product k hk]
    _ = pgf_map pgf_x ^ k * ∏ j ∈ Finset.Icc 1 k, pgf_map (pgf_F j) := by
      unfold pgf_map
      rw [map_mul, map_pow, map_prod]
    _ = _ := by
      simp_rw [pgf_map_F, pgf_r_eq_U]
      simp_rw [mul_div_assoc]
      rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc]
      have hcard : k + 1 - 1 = k := by omega
      rw [hcard]
      ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pgf_PP_triples](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma pgf_PP_triples (k : ℕ) :
  PowerSeries.mk (fun n => ∑ w ∈ Finset.univ.filter
    (fun w : Fin n → Fin k => IsSurjectiveRestrictedGrowthString w),
    Polynomial.X ^ pgf_peakTriples w) = pgf_PP k := by
  apply PowerSeries.ext
  intro n
  simp only [pgf_PP, PowerSeries.coeff_mk]
  apply Finset.sum_congr rfl
  intro w _
  rw [pgf_peakTriples_eq_peak]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[peak_generating_function_set_partitions](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
lemma peak_generating_function_set_partitions
  {k : ℕ}
  {t x q : FractionRing (PowerSeries (Polynomial ℤ))}
-- given
  (hk : 1 ≤ k)
  (hx : x = algebraMap (PowerSeries (Polynomial ℤ)) (FractionRing (PowerSeries (Polynomial ℤ))) PowerSeries.X)
  (hq : q = algebraMap (PowerSeries (Polynomial ℤ)) (FractionRing (PowerSeries (Polynomial ℤ))) (PowerSeries.C Polynomial.X))
  (ht : t = 1 + x ^ 2 * (1 - q) / 2) :
-- imply
  let U : ℤ → FractionRing (PowerSeries (Polynomial ℤ)) := by
-- proof
  dsimp only
  subst x
  subst q
  subst t
  change pgf_map (PowerSeries.mk (fun n => ∑ w ∈ Finset.univ.filter
    (fun w : Fin n → Fin k => IsSurjectiveRestrictedGrowthString w),
    Polynomial.X ^ pgf_peakTriples w)) = _
  rw [pgf_PP_triples]
  simpa [pgf_map, pgf_x, pgf_q, pgf_t, pgf_U] using pgf_map_PP_closed k hk

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
