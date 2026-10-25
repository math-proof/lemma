import Mathlib
import sympy.Basic
import Def.NumberTheory.EngelExpansion.Part3
open EngelExpansion


namespace EngelExpansion

/--
[negRem_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EngelExpansion.lean)
-/
@[path]
lemma negRem_eq_iff
  {n k u : ℕ}
-- given
  (hk : k ≠ 0) :
-- imply
  negRem n k = u ↔ u < k ∧ k ∣ n + u := by
-- proof
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  have hr_lt : n % k < k := Nat.mod_lt n hkpos
  set r := n % k with hr_def
  simp only [negRem, hr_def.symm]
  constructor
  · intro h
    have huk : u < k := by
      rw [← h]
      exact Nat.mod_lt _ hkpos
    refine ⟨huk, ?_⟩
    rw [Nat.dvd_iff_mod_eq_zero]
    conv_lhs => rw [← h, Nat.add_mod, Nat.mod_mod, ← hr_def]
    by_cases hr0 : r = 0
    · rw [hr0]
      simp
    · have hkr : k - r < k := by omega
      rw [Nat.mod_eq_of_lt hkr]
      have hsum : r + (k - r) = k := by omega
      rw [hsum]
      exact Nat.mod_self k
  · rintro ⟨huk, hdvd⟩
    have hmod : (r + u) % k = 0 := by
      have h1 : (n + u) % k = 0 := Nat.mod_eq_zero_of_dvd hdvd
      rwa [Nat.add_mod, Nat.mod_eq_of_lt huk, ← hr_def] at h1
    have hdvd2 : k ∣ r + u := Nat.dvd_iff_mod_eq_zero.mpr hmod
    obtain ⟨q, hq⟩ := hdvd2
    have hlt : r + u < 2 * k := by omega
    have hq_le : q ≤ 1 := by
      by_contra hc
      have hc' : 1 < q := by omega
      have hle : k * 2 ≤ k * q := Nat.mul_le_mul_left k hc'
      omega
    have hq01 : q = 0 ∨ q = 1 := by omega
    obtain rfl | rfl := hq01
    · rw [Nat.mul_zero] at hq
      have hr0 : r = 0 := by omega
      have hu0 : u = 0 := by omega
      rw [hr0, hu0]
      simp
    · have hrr : r = k - u := by omega
      rw [hrr, Nat.sub_sub_self (le_of_lt huk), Nat.mod_eq_of_lt huk]

end EngelExpansion

namespace EngelExpansion

/--
[traj_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EngelExpansion.lean)
-/
@[path]
lemma traj_zero
  {n a : ℕ} :
-- imply
  traj n a 0 = a :=
-- proof
  rfl

end EngelExpansion

namespace EngelExpansion

/--
[traj_succ_of_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EngelExpansion.lean)
-/
@[path]
lemma traj_succ_of_eq_zero
  {n a j : ℕ}
-- given
  (h : traj n a j = 0) :
-- imply
  traj n a (j + 1) = 0 := by
-- proof
  simp only [traj, ite_eq_left h]

end EngelExpansion

namespace EngelExpansion

/--
[traj_succ_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EngelExpansion.lean)
-/
@[path]
lemma traj_succ_of_ne_zero
  {n a j : ℕ}
-- given
  (h : traj n a j ≠ 0) :
-- imply
  traj n a (j + 1) = negRem n (traj n a j) := by
-- proof
  simp only [traj, ite_eq_right h]

end EngelExpansion

namespace EngelExpansion

/--
[traj_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EngelExpansion.lean)
-/
@[path]
lemma traj_one
  {n t : ℕ}
-- given
  (ht : t ≠ 0) :
-- imply
  traj n t 1 = negRem n t := by
-- proof
  have h01 : (1 : ℕ) = 0 + 1 := rfl
  have h0 : traj n t 0 ≠ 0 := by
    rwa [traj_zero]
  rw [h01, traj_succ_of_ne_zero h0, traj_zero]

end EngelExpansion

namespace EngelExpansion

/--
[length_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EngelExpansion.lean)
-/
@[path]
lemma length_pos
  {n a : ℕ} :
-- imply
  1 ≤ length n a :=
-- proof
  (Nat.find_spec (exists_traj_eq_zero_pos n a)).1

end EngelExpansion

namespace EngelExpansion

/--
[traj_length_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EngelExpansion.lean)
-/
@[path]
lemma traj_length_eq_zero
  {n a : ℕ} :
-- imply
  traj n a (length n a) = 0 :=
-- proof
  (Nat.find_spec (exists_traj_eq_zero_pos n a)).2

end EngelExpansion

namespace EngelExpansion

/--
[length_le_of_traj_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EngelExpansion.lean)
-/
@[path]
lemma length_le_of_traj_eq_zero
  {n a j : ℕ}
-- given
  (hj : 1 ≤ j)
  (h : traj n a j = 0) :
-- imply
  length n a ≤ j :=
-- proof
  Nat.find_min' _ ⟨hj, h⟩

end EngelExpansion

namespace EngelExpansion

/--
[traj_ne_zero_of_lt_length](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EngelExpansion.lean)
-/
@[path]
lemma traj_ne_zero_of_lt_length
  {n a j : ℕ}
-- given
  (hj : 1 ≤ j)
  (hlt : j < length n a) :
-- imply
  traj n a j ≠ 0 := by
-- proof
  have hneg := Nat.find_min _ hlt
  intro h0
  exact hneg ⟨hj, h0⟩

end EngelExpansion

namespace EngelExpansion

/--
[length_le_maxLength](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EngelExpansion.lean)
-/
@[path]
lemma length_le_maxLength
  {n a : ℕ}
-- given
  (ha : a ∈ Finset.Icc 1 n) :
-- imply
  length n a ≤ maxLength n :=
-- proof
  Finset.le_sup ha

end EngelExpansion

namespace EngelExpansion

/--
[maxLength_le_of_forall](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EngelExpansion.lean)
-/
@[path]
lemma maxLength_le_of_forall
  {n L : ℕ}
-- given
  (h : ∀ a ∈ Finset.Icc 1 n, length n a ≤ L) :
-- imply
  maxLength n ≤ L :=
-- proof
  Finset.sup_le h

end EngelExpansion

/--
[negRem_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EngelExpansion.lean)
-/
@[path]
private lemma negRem_lt_eq
  {n k : ℕ}
-- given
  (hk : k ≠ 0) :
-- imply
  negRem n k < k := by
-- proof
  apply EngelExpansion.negRem_lt hk

/--
[exists_traj_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EngelExpansion.lean)
-/
@[path]
private lemma exists_traj_eq_zero_eq
  {n a : ℕ} :
-- imply
  ∃ i ≤ a + 1, traj n a i = 0 := by
-- proof
  apply EngelExpansion.exists_traj_eq_zero n a

/--
[exists_traj_eq_zero_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EngelExpansion.lean)
-/
@[path]
private lemma exists_traj_eq_zero_pos_eq
  {n a : ℕ} :
-- imply
  ∃ j ≥ 1, traj n a j = 0 := by
-- proof
  apply EngelExpansion.exists_traj_eq_zero_pos n a


-- created on 2026-10-20
-- updated on 2026-10-23
