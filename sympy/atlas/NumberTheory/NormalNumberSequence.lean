/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NormalNumberSequence.lean -/

import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

/-!
# A normal second-order number sequence

This file proves the odd-index sum-of-two-squares identity from L. Goy,
*On Identities for Normal Number Sequences*:
<https://cs.uwaterloo.ca/journals/JIS/VOL19/Goy/goy2.tex>.
-/

namespace MetaMathlibExt

/-- Normal second-order number sequence with nonzero integer coefficients:
`u_1 = 1`, `u_2 = a1`, `u_(n+2) = a1 * u_(n+1) + a2 * u_n`.
Concept `jis_sem_341d671b9a22383202776b02`;
source `jis_source_6670e6fe84c03e3ab211c809`.
The Lean totalization sets `u_0 = 0`; source indices `u_1`, `u_2` are unshifted. -/
def normalSeq (a1 a2 : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | (n + 2) => a1 * normalSeq a1 a2 (n + 1) + a2 * normalSeq a1 a2 n

/-- First source term `u_1 = 1` (the source assumes nonzero coefficients).
Concept `jis_sem_341d671b9a22383202776b02`;
source `jis_source_6670e6fe84c03e3ab211c809`. -/
theorem normalSeq_one (a1 a2 : ℤ) :
    normalSeq a1 a2 1 = 1 := by
  simp [normalSeq]

/-- Second source term `u_2 = a1` (the source assumes nonzero coefficients).
Concept `jis_sem_341d671b9a22383202776b02`;
source `jis_source_6670e6fe84c03e3ab211c809`. -/
theorem normalSeq_two (a1 a2 : ℤ) :
    normalSeq a1 a2 2 = a1 := by
  simp [normalSeq]

/-- General second-order recurrence (the source assumes nonzero coefficients).
Concept `jis_sem_341d671b9a22383202776b02`;
source `jis_source_6670e6fe84c03e3ab211c809`. -/
theorem normalSeq_recurrence (a1 a2 : ℤ) (n : ℕ) :
    normalSeq a1 a2 (n + 2) =
      a1 * normalSeq a1 a2 (n + 1) + a2 * normalSeq a1 a2 n := by
  simp [normalSeq]

/-- Specialization `a1 = a`, `a2 = 1` with `a` a nonzero integer.
Concept `jis_sem_341d671b9a22383202776b02`;
source `jis_source_6670e6fe84c03e3ab211c809`. -/
def normalSeqFib (a : ℤ) : ℕ → ℤ :=
  fun n => normalSeq a 1 n

/-- Addition formula for the specialized sequence; directly supports the
odd-index identity.
Concept `jis_sem_341d671b9a22383202776b02`;
source `jis_source_6670e6fe84c03e3ab211c809`. -/
theorem normalSeqFib_add (a : ℤ) (m n : ℕ) :
    normalSeqFib a (m + n + 1) =
      normalSeqFib a (m + 1) * normalSeqFib a (n + 1) +
        normalSeqFib a m * normalSeqFib a n := by
  have hF0 : normalSeqFib a 0 = 0 := by simp [normalSeqFib, normalSeq]
  have hF1 : normalSeqFib a 1 = 1 := by simp [normalSeqFib, normalSeq]
  have hF2 : normalSeqFib a 2 = a := by simp [normalSeqFib, normalSeq]
  have hrec : ∀ t : ℕ, normalSeqFib a (t + 2) =
      a * normalSeqFib a (t + 1) + normalSeqFib a t := by
    intro t
    simp [normalSeqFib, normalSeq]
  have key : ∀ m : ℕ,
      (∀ n : ℕ, normalSeqFib a (m + n + 1) =
        normalSeqFib a (m + 1) * normalSeqFib a (n + 1) +
          normalSeqFib a m * normalSeqFib a n) ∧
      (∀ n : ℕ, normalSeqFib a (m + n + 2) =
        normalSeqFib a (m + 2) * normalSeqFib a (n + 1) +
          normalSeqFib a (m + 1) * normalSeqFib a n) := by
    intro m
    induction m with
    | zero =>
      constructor
      · intro n
        have hidx : 0 + n + 1 = n + 1 := by ring
        have h01 : (0 : ℕ) + 1 = 1 := by ring
        rw [hidx, h01, hF0, hF1, one_mul, zero_mul, add_zero]
      · intro n
        have hidx : 0 + n + 2 = n + 2 := by ring
        have h02 : (0 : ℕ) + 2 = 2 := by ring
        have h01 : (0 : ℕ) + 1 = 1 := by ring
        rw [hidx, h02, h01, hF2, hF1, one_mul]
        rw [hrec n]
    | succ k ih =>
      obtain ⟨ih1, ih2⟩ := ih
      constructor
      · intro n
        have eA : k + 1 + n + 1 = k + n + 2 := by ring
        have eB : k + 1 + 1 = k + 2 := by ring
        rw [eA, eB]
        exact ih2 n
      · intro n
        have e1 : (k + 1) + n + 2 = (k + n + 1) + 2 := by ring
        have e1b : (k + n + 1) + 1 = k + n + 2 := by ring
        have e4 : (k + 1) + 1 = k + 2 := by ring
        have hFk : normalSeqFib a ((k + 1) + 2) =
            a * normalSeqFib a (k + 2) + normalSeqFib a (k + 1) := by
          have h := hrec (k + 1)
          rw [e4] at h
          exact h
        have hFk2 : normalSeqFib a (k + 2) =
            a * normalSeqFib a (k + 1) + normalSeqFib a k := hrec k
        rw [e1, hrec (k + n + 1), e1b, ih2 n, ih1 n, e4, hFk, hFk2]
        ring
  exact (key m).1 n

/-- Odd-index identity `u_(2n-1) = u_n ^ 2 + u_(n-1) ^ 2` for the specialized
    sequence and `n ≥ 2` (so `2n - 1 ≥ 3`). It remains valid without the
    source's assumption `a ≠ 0`.
Concept `jis_sem_341d671b9a22383202776b02`;
source `jis_source_6670e6fe84c03e3ab211c809`;
statement `jis_225330004269597626fa0967`. -/
theorem normalSeq_odd_identity (a : ℤ) (n : ℕ) (hn : 2 ≤ n) :
    normalSeqFib a (2 * n - 1) =
      (normalSeqFib a n) ^ 2 + (normalSeqFib a (n - 1)) ^ 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hnk : 2 + k = (1 + k) + 1 := by ring
  have e_sub : 2 + k - 1 = 1 + k := by rw [hnk, Nat.add_sub_cancel]
  have hodd : 2 * (2 + k) = ((1 + k) + (1 + k) + 1) + 1 := by ring
  have e_odd : 2 * (2 + k) - 1 = (1 + k) + (1 + k) + 1 := by
    rw [hodd, Nat.add_sub_cancel]
  have f1 : (1 + k) + 1 = 2 + k := by ring
  rw [e_odd, e_sub]
  have h := normalSeqFib_add a (1 + k) (1 + k)
  rw [f1] at h
  rw [h]
  ring

end MetaMathlibExt
