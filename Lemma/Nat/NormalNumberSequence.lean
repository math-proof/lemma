import Mathlib
import sympy.Basic
import Def.NumberTheory.NormalNumberSequence
open MetaMathlibExt


namespace MetaMathlibExt

/--
[normalSeq_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NormalNumberSequence.lean)
-/
@[path]
lemma normalSeq_one
  {a1 a2 : ℤ} :
-- imply
  normalSeq a1 a2 1 = 1 := by
-- proof
  simp [normalSeq]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[normalSeq_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NormalNumberSequence.lean)
-/
@[path]
lemma normalSeq_two
  {a1 a2 : ℤ} :
-- imply
  normalSeq a1 a2 2 = a1 := by
-- proof
  simp [normalSeq]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[normalSeq_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NormalNumberSequence.lean)
-/
@[path]
lemma normalSeq_recurrence
  {a1 a2 : ℤ}
  {n : ℕ} :
-- imply
  normalSeq a1 a2 (n + 2) =
    a1 * normalSeq a1 a2 (n + 1) + a2 * normalSeq a1 a2 n := by
-- proof
  simp [normalSeq]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[normalSeqFib_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NormalNumberSequence.lean)
-/
@[path]
lemma normalSeqFib_add
  {a : ℤ}
  {m n : ℕ} :
-- imply
  normalSeqFib a (m + n + 1) =
    normalSeqFib a (m + 1) * normalSeqFib a (n + 1) +
    normalSeqFib a m * normalSeqFib a n := by
-- proof
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
          rwa [e4] at h
        have hFk2 : normalSeqFib a (k + 2) =
          a * normalSeqFib a (k + 1) + normalSeqFib a k := hrec k
        rw [e1, hrec (k + n + 1), e1b, ih2 n, ih1 n, e4, hFk, hFk2]
        ring
  exact (key m).1 n

end MetaMathlibExt

namespace MetaMathlibExt

/--
[normalSeq_odd_identity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NormalNumberSequence.lean)
-/
@[path]
lemma normalSeq_odd_identity
  {a : ℤ}
  {n : ℕ}
-- given
  (hn : 2 ≤ n) :
-- imply
  normalSeqFib a (2 * n - 1) =
    (normalSeqFib a n) ^ 2 + (normalSeqFib a (n - 1)) ^ 2 := by
-- proof
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


-- created on 2026-10-20
-- updated on 2026-10-23
