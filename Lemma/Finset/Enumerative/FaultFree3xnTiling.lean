import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.FaultFree3xnTiling.Part21
open MetaMathlibExt


namespace MetaMathlibExt

/--
[ff3_adjacent_comm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean)
-/
@[path]
private lemma ff3_adjacent_comm {n : ℕ} {x y : TilingCell n} :
  TilingCell.Adjacent x y ↔ TilingCell.Adjacent y x := by
  simp only [TilingCell.Adjacent, eq_comm]
  tauto

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ff3_columnCount_profiles](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean)
-/
@[path]
private lemma ff3_columnCount_profiles (p q : ff3Profile) :
  ff3ColumnCount (ff3ProfileRows p) (ff3ProfileRows q) = ff3Matrix ℕ p q := by
  fin_cases p <;> fin_cases q <;> decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ff3_columnCount_left](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean)
-/
@[path]
private lemma ff3_columnCount_left (p : ff3Profile) :
  ff3ColumnCount ∅ (ff3ProfileRows p) = ff3Boundary ℕ p := by
  fin_cases p <;> decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ff3_columnCount_right](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean)
-/
@[path]
private lemma ff3_columnCount_right (p : ff3Profile) :
  ff3ColumnCount (ff3ProfileRows p) ∅ = ff3Boundary ℕ p := by
  fin_cases p <;> decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ff3_columnCount_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean)
-/
@[path]
private lemma ff3_columnCount_empty : ff3ColumnCount ∅ ∅ = 3 := by
  decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ff3_card_path_rows](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean)
-/
@[path]
private lemma ff3_card_path_rows (p : ff3Profile) : ∀ n,
  Nat.card (ff3Path (ff3ProfileRows p) n) = ff3TailCount ℕ n p := by
  intro n
  induction n generalizing p with
  | zero =>
    change Nat.card (ff3ColumnFilling (ff3ProfileRows p) ∅) = _
    rw [Nat.card_eq_fintype_card, show Fintype.card
      (ff3ColumnFilling (ff3ProfileRows p) ∅) =
        ff3ColumnCount (ff3ProfileRows p) ∅ from rfl, ff3_columnCount_right]
    classical
    simp [ff3TailCount, Matrix.one_apply]
  | succ n ih =>
    change Nat.card (Σ q : ff3Profile,
      ff3ColumnFilling (ff3ProfileRows p) (ff3ProfileRows q) ×
        ff3Path (ff3ProfileRows q) n) = _
    rw [Nat.card_sigma]
    simp_rw [Nat.card_prod]
    change (∑ q : ff3Profile,
      Nat.card (ff3ColumnFilling (ff3ProfileRows p) (ff3ProfileRows q)) *
        Nat.card (ff3Path (ff3ProfileRows q) n)) = _
    simp_rw [Nat.card_eq_fintype_card]
    change (∑ q : ff3Profile,
      ff3ColumnCount (ff3ProfileRows p) (ff3ProfileRows q) *
        Fintype.card (ff3Path (ff3ProfileRows q) n)) = _
    simp_rw [← Nat.card_eq_fintype_card, ff3_columnCount_profiles, ih]
    simp only [ff3TailCount, pow_succ', Matrix.mul_apply]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ff3_card_path_empty_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean)
-/
@[path]
private lemma ff3_card_path_empty_succ (n : ℕ) :
  Nat.card (ff3Path ∅ (n + 1)) = ff3TransferCount ℕ n := by
  change Nat.card (Σ p : ff3Profile,
    ff3ColumnFilling ∅ (ff3ProfileRows p) × ff3Path (ff3ProfileRows p) n) = _
  rw [Nat.card_sigma]
  simp_rw [Nat.card_prod]
  change (∑ p : ff3Profile, Nat.card (ff3ColumnFilling ∅ (ff3ProfileRows p)) *
    Nat.card (ff3Path (ff3ProfileRows p) n)) = _
  simp_rw [Nat.card_eq_fintype_card]
  change (∑ p : ff3Profile, ff3ColumnCount ∅ (ff3ProfileRows p) *
    Fintype.card (ff3Path (ff3ProfileRows p) n)) = _
  simp_rw [← Nat.card_eq_fintype_card, ff3_columnCount_left, ff3_card_path_rows]
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ff3_card_path_empty_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean)
-/
@[path]
private lemma ff3_card_path_empty_zero : Nat.card (ff3Path ∅ 0) = 3 := by
  change Nat.card (ff3ColumnFilling ∅ ∅) = 3
  rwa [Nat.card_eq_fintype_card]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ff3_matrix_cast_entry](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean)
-/
@[path]
private lemma ff3_matrix_cast_entry (p q : ff3Profile) :
  ((ff3Matrix ℕ p q : ℕ) : ℤ) = ff3Matrix ℤ p q := by
  fin_cases p <;> fin_cases q <;> rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ff3_boundary_cast](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean)
-/
@[path]
private lemma ff3_boundary_cast (p : ff3Profile) :
  ((ff3Boundary ℕ p : ℕ) : ℤ) = ff3Boundary ℤ p := by
  fin_cases p <;> rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ff3_matrix_pow_cast](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean)
-/
@[path]
private lemma ff3_matrix_pow_cast (n : ℕ) (p q : ff3Profile) :
  (((ff3Matrix ℕ ^ n) p q : ℕ) : ℤ) = (ff3Matrix ℤ ^ n) p q := by
  have hmap := Matrix.map_pow (ff3Matrix ℕ) Int.ofNatHom n
  have hM : (ff3Matrix ℕ).map (⇑Int.ofNatHom) = ff3Matrix ℤ := by
    ext i j
    exact ff3_matrix_cast_entry i j
  have h := congrFun (congrFun hmap p) q
  rw [hM] at h
  change (((ff3Matrix ℕ ^ n) p q : ℕ) : ℤ) = (ff3Matrix ℤ ^ n) p q at h
  exact h

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ff3_transfer_cast](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean)
-/
@[path]
private lemma ff3_transfer_cast (n : ℕ) :
  ((ff3TransferCount ℕ n : ℕ) : ℤ) = ff3TransferCount ℤ n := by
  simp only [ff3TransferCount, ff3TailCount, Nat.cast_sum, Nat.cast_mul]
  simp_rw [ff3_matrix_pow_cast, ff3_boundary_cast]
set_option maxHeartbeats 1000000 in

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ff3_matrix_annihilates](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean)
-/
@[path]
private lemma ff3_matrix_annihilates (p q : ff3Profile) :
  (ff3Matrix ℤ ^ 5) p q - (ff3Matrix ℤ ^ 4) p q -
    4 * (ff3Matrix ℤ ^ 3) p q + (ff3Matrix ℤ ^ 2) p q + ff3Matrix ℤ p q = 0 := by
  fin_cases p <;> fin_cases q <;> decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ff3_matrix_polynomial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean)
-/
@[path]
private lemma ff3_matrix_polynomial :
  ff3Matrix ℤ ^ 5 = ff3Matrix ℤ ^ 4 + (4 : ℤ) • ff3Matrix ℤ ^ 3 -
    ff3Matrix ℤ ^ 2 - ff3Matrix ℤ := by
  ext p q
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply]
  simp only [smul_eq_mul]
  have h := ff3_matrix_annihilates p q
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ff3_matrix_power_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean)
-/
@[path]
private lemma ff3_matrix_power_recurrence (n : ℕ) :
  ff3Matrix ℤ ^ (n + 5) = ff3Matrix ℤ ^ (n + 4) +
    (4 : ℤ) • ff3Matrix ℤ ^ (n + 3) - ff3Matrix ℤ ^ (n + 2) -
      ff3Matrix ℤ ^ (n + 1) := by
  rw [pow_add, pow_add, pow_add, pow_add, pow_add, ff3_matrix_polynomial]
  simp only [mul_sub, mul_add, mul_smul_comm]
  simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ff3_transfer_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean)
-/
@[path]
private lemma ff3_transfer_recurrence (n : ℕ) :
  ff3TransferCount ℤ (n + 5) = ff3TransferCount ℤ (n + 4) +
    4 * ff3TransferCount ℤ (n + 3) - ff3TransferCount ℤ (n + 2) -
      ff3TransferCount ℤ (n + 1) := by
  have h := ff3_matrix_power_recurrence n
  let L : Matrix ff3Profile ff3Profile ℤ → ℤ := fun A =>
    ∑ p, ff3Boundary ℤ p * ∑ q, A p q * ff3Boundary ℤ q
  have L_add (A B : Matrix ff3Profile ff3Profile ℤ) : L (A + B) = L A + L B := by
    simp [L, Matrix.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
  have L_sub (A B : Matrix ff3Profile ff3Profile ℤ) : L (A - B) = L A - L B := by
    simp [L, Matrix.sub_apply, sub_mul, mul_sub, Finset.sum_sub_distrib]
  have L_smul (A : Matrix ff3Profile ff3Profile ℤ) : L ((4 : ℤ) • A) = 4 * L A := by
    simp only [L, Matrix.smul_apply]
    simp only [smul_eq_mul]
    simp_rw [Finset.mul_sum]
    ring_nf
  change L (ff3Matrix ℤ ^ (n + 5)) = L (ff3Matrix ℤ ^ (n + 4)) +
    4 * L (ff3Matrix ℤ ^ (n + 3)) - L (ff3Matrix ℤ ^ (n + 2)) -
      L (ff3Matrix ℤ ^ (n + 1))
  rw [h]
  rw [L_sub, L_sub, L_add, L_smul]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ff3_transfer_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean)
-/
@[path]
private lemma ff3_transfer_zero : ff3TransferCount ℕ 0 = 13 := by
decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ff3_transfer_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean)
-/
@[path]
private lemma ff3_transfer_one : ff3TransferCount ℕ 1 = 26 := by
decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ff3_transfer_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean)
-/
@[path]
private lemma ff3_transfer_two : ff3TransferCount ℕ 2 = 66 := by
decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ff3_transfer_three](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean)
-/
@[path]
private lemma ff3_transfer_three : ff3TransferCount ℕ 3 = 154 := by
decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ff3_transfer_four](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean)
-/
@[path]
private lemma ff3_transfer_four : ff3TransferCount ℕ 4 = 380 := by
decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ff3_model_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean)
-/
@[path]
private lemma ff3_model_recurrence (n : ℕ) :
  (ff3ModelCount (n + 7) : ℤ) = (ff3ModelCount (n + 6) : ℤ) +
    4 * (ff3ModelCount (n + 5) : ℤ) - (ff3ModelCount (n + 4) : ℤ) -
      (ff3ModelCount (n + 3) : ℤ) := by
  change ((ff3TransferCount ℕ (n + 5) : ℕ) : ℤ) =
    (ff3TransferCount ℕ (n + 4) : ℤ) + 4 * (ff3TransferCount ℕ (n + 3) : ℤ) -
      (ff3TransferCount ℕ (n + 2) : ℤ) - (ff3TransferCount ℕ (n + 1) : ℤ)
  simp_rw [ff3_transfer_cast]
  exact ff3_transfer_recurrence n

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ff3_model_eq_tilingCount](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean)
-/
@[path]
private lemma ff3_model_eq_tilingCount :
  ∀ n : ℕ, 1 ≤ n → (ff3ModelCount n : ℤ) = tilingCount n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hsmall : n ≤ 6
    · interval_cases n <;>
      simp_all [ff3ModelCount, tilingCount, ff3_transfer_zero, ff3_transfer_one,
        ff3_transfer_two, ff3_transfer_three, ff3_transfer_four]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
      rw [tilingCount]
      rw [← ih (m + 6) (by omega) (by omega), ← ih (m + 5) (by omega) (by omega),
        ← ih (m + 4) (by omega) (by omega), ← ih (m + 3) (by omega) (by omega)]
      exact ff3_model_recurrence m

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ff3_vertical_count_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean)
-/
@[path]
private lemma ff3_vertical_count_succ (n : ℕ) :
  verticalFaultFreeTilingCount (n + 1) = ff3ModelCount (n + 1) := by
  unfold verticalFaultFreeTilingCount
  rw [Nat.card_congr (ff3TilingPathEquiv n)]
  cases n with
  | zero => simpa [ff3ModelCount] using ff3_card_path_empty_zero
  | succ n => simpa [ff3ModelCount] using ff3_card_path_empty_succ n

end MetaMathlibExt

namespace MetaMathlibExt

/--
[fault_free_3xn_tiling_recursion](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean)
-/
@[path]
lemma fault_free_3xn_tiling_recursion
  :
-- imply
  ∀ n : ℕ, 1 ≤ n → (verticalFaultFreeTilingCount n : ℤ) = tilingCount n := by
-- proof
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [ff3_vertical_count_succ]
  exact ff3_model_eq_tilingCount (m + 1) (by omega)

end MetaMathlibExt

/--
[isSquareOrDomino_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean)
-/
@[path]
private lemma isSquareOrDomino_iff_eq
  {n : ℕ}
  {d : Finset (TilingCell n)} :
-- imply
  IsSquareOrDomino d ↔
    (∃ x, d = {x}) ∨
    ∃ x y, x ≠ y ∧ TilingCell.Adjacent x y ∧ d = {x, y} := by
-- proof
  apply MetaMathlibExt.isSquareOrDomino_iff d


-- created on 2026-10-20
-- updated on 2026-10-26
