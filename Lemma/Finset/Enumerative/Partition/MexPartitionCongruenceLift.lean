import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Combinatorics.Enumerative.Partition.MexPartitionCongruenceLift.Part5
open MetaMathlibExt


namespace MetaMathlibExt

/--
[mex_prefix_le_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/MexPartitionCongruenceLift.lean)
-/
@[path]
private lemma mex_prefix_le_iff {N : ℕ} (c : ℕ → ℕ) (j : ℕ)
  (p : Nat.Partition N) :
  mex_prefix c j ≤ p.parts ↔ ∀ i < j, c i ∈ p.parts := by
  have hnodup : (mex_prefix c j).Nodup := (Finset.image c (Finset.range j)).nodup
  rw [Multiset.le_iff_subset hnodup]
  constructor
  · intro h i hi
    apply h
    simp only [mex_prefix, Finset.mem_val, Finset.mem_image, Finset.mem_range]
    exact ⟨i, hi, rfl⟩
  · intro h x hx
    simp only [mex_prefix, Finset.mem_val, Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact h i hi

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mex_prefix_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/MexPartitionCongruenceLift.lean)
-/
@[path]
private lemma mex_prefix_pos (c : ℕ → ℕ) (hcpos : ∀ i, 0 < c i) (j : ℕ) :
  ∀ x ∈ mex_prefix c j, 0 < x := by
  intro x hx
  simp only [mex_prefix, Finset.mem_val, Finset.mem_image] at hx
  obtain ⟨i, -, rfl⟩ := hx
  exact hcpos i

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mex_prefix_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/MexPartitionCongruenceLift.lean)
-/
@[path]
private lemma mex_prefix_sum (c : ℕ → ℕ) (hc : Function.Injective c) (j : ℕ) :
  (mex_prefix c j).sum = ∑ i ∈ Finset.range j, c i := by
  rw [mex_prefix, Finset.sum_val]
  exact Finset.sum_image (Set.injOn_of_injective hc)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mex_prefix_succ_le_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/MexPartitionCongruenceLift.lean)
-/
@[path]
private lemma mex_prefix_succ_le_iff {N : ℕ} (c : ℕ → ℕ) (j : ℕ)
  (p : Nat.Partition N) :
  mex_prefix c (j + 1) ≤ p.parts ↔ mex_prefix c j ≤ p.parts ∧ c j ∈ p.parts := by
  rw [mex_prefix_le_iff, mex_prefix_le_iff]
  constructor
  · intro h
    exact ⟨fun i hi => h i (by omega), h j (by omega)⟩
  · rintro ⟨h, hj⟩ i hi
    by_cases hij : i < j
    · exact h i hij
    · have : i = j := by omega
      subst i
      exact hj

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mex_required_card_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/MexPartitionCongruenceLift.lean)
-/
@[path]
private lemma mex_required_card_dvd (m a b n T : ℕ) (hb : b < a)
  (hbase : ∀ q : ℕ, m ∣ Fintype.card (Nat.Partition (a * q + b)))
  (R : Multiset ℕ) (hpos : ∀ x ∈ R, 0 < x) (hsum : R.sum = a * T) :
  m ∣ (Finset.univ.filter fun p : Nat.Partition (a * n + b) => R ≤ p.parts).card := by
  classical
  by_cases hT : T ≤ n
  · have hmul : a * T ≤ a * n := Nat.mul_le_mul_left a hT
    have hRle : R.sum ≤ a * n + b := by
      rw [hsum]
      omega
    have hindex : a * n + b - R.sum = a * (n - T) + b := by
      rw [hsum, Nat.sub_add_comm hmul, ← Nat.mul_sub_left_distrib]
    have hcard :
      (Finset.univ.filter fun p : Nat.Partition (a * n + b) => R ≤ p.parts).card =
        Fintype.card (Nat.Partition (a * n + b - R.sum)) := by
      calc
        _ = Fintype.card {p : Nat.Partition (a * n + b) // R ≤ p.parts} :=
          (Fintype.card_subtype _).symm
        _ = _ := Fintype.card_congr (mex_remove_equiv R hpos hRle)
    rw [hcard, hindex]
    exact hbase (n - T)
  · have hnT : n < T := Nat.lt_of_not_ge hT
    have hNlt : a * n + b < R.sum := by
      calc
        a * n + b < a * n + a := Nat.add_lt_add_left hb _
        _ = a * (n + 1) := by ring
        _ ≤ a * T := Nat.mul_le_mul_left a (by omega)
        _ = R.sum := hsum.symm
    have hempty :
      (Finset.univ.filter fun p : Nat.Partition (a * n + b) => R ≤ p.parts) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      have hR := (Finset.mem_filter.mp hp).2
      have hcancel := Multiset.sub_add_cancel hR
      have hs := congrArg Multiset.sum hcancel
      rw [Multiset.sum_add, p.parts_sum] at hs
      omega
    simp [hempty]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mex_linear_candidate_strict](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/MexPartitionCongruenceLift.lean)
-/
@[path]
private lemma mex_linear_candidate_strict (A : ℕ) (hA : 0 < A) :
  StrictMono (mex_linear_candidate A) := by
  intro i j hij
  apply Nat.mul_lt_mul_of_pos_left _ hA
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mex_odd_candidate_strict](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/MexPartitionCongruenceLift.lean)
-/
@[path]
private lemma mex_odd_candidate_strict (A : ℕ) (hA : 0 < A) :
  StrictMono (mex_odd_candidate A) := by
  intro i j hij
  apply Nat.mul_lt_mul_of_pos_left _ hA
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mex_linear_candidate_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/MexPartitionCongruenceLift.lean)
-/
@[path]
private lemma mex_linear_candidate_pos (A : ℕ) (hA : 0 < A) (i : ℕ) :
  0 < mex_linear_candidate A i :=
Nat.mul_pos hA (by omega)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mex_odd_candidate_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/MexPartitionCongruenceLift.lean)
-/
@[path]
private lemma mex_odd_candidate_pos (A : ℕ) (hA : 0 < A) (i : ℕ) :
  0 < mex_odd_candidate A i :=
Nat.mul_pos hA (by omega)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mex_scaled_prefix_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/MexPartitionCongruenceLift.lean)
-/
@[path]
private lemma mex_scaled_prefix_sum (a t : ℕ) (d : ℕ → ℕ)
  (hc : StrictMono fun i => (a * t) * d i) (j : ℕ) :
  (mex_prefix (fun i => (a * t) * d i) j).sum =
    a * (t * ∑ i ∈ Finset.range j, d i) := by
  rw [mex_prefix_sum _ hc.injective, ← Finset.mul_sum]
  simp only [mul_assoc]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mex_linear_candidate_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/MexPartitionCongruenceLift.lean)
-/
@[path]
private lemma mex_linear_candidate_iff (A μ : ℕ) (hA : 0 < A) :
  (0 < μ ∧ μ % A = A % A) ↔ ∃ j, μ = mex_linear_candidate A j := by
  rw [Nat.mod_self]
  constructor
  · rintro ⟨hμ, hmod⟩
    obtain ⟨q, rfl⟩ := (Nat.dvd_iff_mod_eq_zero.mpr hmod)
    have hq : q ≠ 0 := by
      intro hq
      subst q
      simp at hμ
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
    exact ⟨j, by simp [mex_linear_candidate]⟩
  · rintro ⟨j, rfl⟩
    exact ⟨mex_linear_candidate_pos A hA j, by simp [mex_linear_candidate]⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mex_linear_selected_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/MexPartitionCongruenceLift.lean)
-/
@[path]
private lemma mex_linear_selected_iff (A j : ℕ) (hA : 0 < A) :
  mex_linear_candidate A j % (2 * A) = A % (2 * A) ↔ Even j := by
  have hlt : A < 2 * A := by
    calc
      A = A * 1 := by simp
      _ < A * 2 := (Nat.mul_lt_mul_left hA).2 (by omega)
      _ = 2 * A := by ac_rfl
  have hleft : mex_linear_candidate A j % (2 * A) = A * ((j + 1) % 2) := by
    rw [mex_linear_candidate, mul_comm 2 A]
    exact Nat.mul_mod_mul_left A (j + 1) 2
  rw [hleft, Nat.mod_eq_of_lt hlt]
  have hcancel : A * ((j + 1) % 2) = A ↔ (j + 1) % 2 = 1 := by
    simpa only [mul_one] using
      (Nat.mul_left_cancel_iff hA (m := (j + 1) % 2) (k := 1))
  rw [hcancel, Nat.even_iff]
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mex_odd_candidate_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/MexPartitionCongruenceLift.lean)
-/
@[path]
private lemma mex_odd_candidate_iff (A μ : ℕ) (hA : 0 < A) :
  (0 < μ ∧ μ % (2 * A) = A % (2 * A)) ↔ ∃ j, μ = mex_odd_candidate A j := by
  have hlt : A < 2 * A := by
    calc
      A = A * 1 := by simp
      _ < A * 2 := (Nat.mul_lt_mul_left hA).2 (by omega)
      _ = 2 * A := by ac_rfl
  constructor
  · rintro ⟨_hμ, hmod⟩
    have hmodA : μ % (2 * A) = A := hmod.trans (Nat.mod_eq_of_lt hlt)
    have hdecomp := Nat.div_add_mod μ (2 * A)
    rw [hmodA] at hdecomp
    let q := μ / (2 * A)
    refine ⟨q, ?_⟩
    calc
      μ = 2 * A * q + A := by simpa only [q] using hdecomp.symm
      _ = mex_odd_candidate A q := by simp only [mex_odd_candidate]; ring
  · rintro ⟨j, rfl⟩
    refine ⟨mex_odd_candidate_pos A hA j, ?_⟩
    calc
      mex_odd_candidate A j % (2 * A) = A * ((2 * j + 1) % 2) := by
        rw [mex_odd_candidate, mul_comm 2 A]
        exact Nat.mul_mod_mul_left A (2 * j + 1) 2
      _ = A := by
        have hodd : (2 * j + 1) % 2 = 1 := by omega
        rw [hodd, mul_one]
      _ = A % (2 * A) := (Nat.mod_eq_of_lt hlt).symm

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mex_odd_selected_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/MexPartitionCongruenceLift.lean)
-/
@[path]
private lemma mex_odd_selected_iff (A j : ℕ) (hA : 0 < A) :
  mex_odd_candidate A j % (2 * (2 * A)) = A % (2 * (2 * A)) ↔ Even j := by
  have hdenom : 2 * (2 * A) = A * 4 := by ring
  have hlt : A < 2 * (2 * A) := by
    rw [hdenom]
    calc
      A = A * 1 := by simp
      _ < A * 4 := (Nat.mul_lt_mul_left hA).2 (by omega)
  have hleft : mex_odd_candidate A j % (2 * (2 * A)) = A * ((2 * j + 1) % 4) := by
    rw [mex_odd_candidate, hdenom]
    exact Nat.mul_mod_mul_left A (2 * j + 1) 4
  rw [hleft, Nat.mod_eq_of_lt hlt]
  have hcancel : A * ((2 * j + 1) % 4) = A ↔ (2 * j + 1) % 4 = 1 := by
    simpa only [mul_one] using
      (Nat.mul_left_cancel_iff hA (m := (2 * j + 1) % 4) (k := 1))
  rw [hcancel, Nat.even_iff]
  omega

end MetaMathlibExt

/--
[mesh_partition_congruence_lift](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/MexPartitionCongruenceLift.lean)
-/
@[path]
private lemma mesh_partition_congruence_lift_eq
  {m a b : ℕ}
-- given
  (hm : 0 < m)
  (ha : 0 < a)
  (hb : b < a)
  (hbase : ∀ n : ℕ, m ∣ Fintype.card (Nat.Partition (a * n + b))) :
-- imply
  ∀ t : ℕ, 0 < t →
    (∀ n : ℕ, m ∣ (@Finset.filter (Nat.Partition (a * n + b))
    (fun lam => ∃ μ : ℕ, 0 < μ ∧ μ % (a * t) = (a * t) % (a * t) ∧
    μ ∉ lam.parts ∧
    (∀ k : ℕ, 0 < k → k < μ → k % (a * t) = (a * t) % (a * t) →
    k ∈ lam.parts) ∧
    μ % (2 * (a * t)) = (a * t) % (2 * (a * t)))
    (Classical.decPred _) Finset.univ).card) ∧
    (∀ n : ℕ, m ∣ (@Finset.filter (Nat.Partition (a * n + b))
    (fun lam => ∃ μ : ℕ, 0 < μ ∧ μ % (2 * a * t) = (a * t) % (2 * a * t) ∧
    μ ∉ lam.parts ∧
    (∀ k : ℕ, 0 < k → k < μ → k % (2 * a * t) = (a * t) % (2 * a * t) →
    k ∈ lam.parts) ∧
    μ % (2 * (2 * a * t)) = (a * t) % (2 * (2 * a * t)))
    (Classical.decPred _) Finset.univ).card) := by
-- proof
  apply MetaMathlibExt.mesh_partition_congruence_lift m a b hm ha hb hbase


-- created on 2026-10-20
-- updated on 2026-10-26
