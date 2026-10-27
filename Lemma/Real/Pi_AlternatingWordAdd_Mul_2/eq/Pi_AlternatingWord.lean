import Mathlib
import Initialize.Tactic.Attr.Basic
open List


namespace CoxeterSystem

/--
[wordProd_alternatingWord_periodic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DihedralLengthBound.lean)
-/
@[path]
private lemma wordProd_alternatingWord_periodic
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {i i' : B}
  {n : ℕ} :
-- imply
  cs.wordProd (alternatingWord i i' (n + M i i' * 2)) = cs.wordProd (alternatingWord i i' n) := by
-- proof
  simp only [cs.prod_alternatingWord_eq_mul_pow]
  have hparity : Even (n + M i i' * 2) ↔ Even n := by
    constructor
    ·
      intro ⟨k, hk⟩
      exact ⟨k - M i i', by omega⟩
    ·
      intro ⟨k, hk⟩
      exact ⟨k + M i i', by omega⟩
  have hdiv : (n + M i i' * 2) / 2 = n / 2 + M i i' := by omega
  congr 1
  · by_cases h : Even n <;> simp [h, hparity.mpr, hparity] at *
  · rw [hdiv, pow_add, pow_mul_comm, cs.simple_mul_simple_pow i i', one_mul]

end CoxeterSystem

namespace CoxeterSystem

/--
[length_wordProd_alternatingWord_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DihedralLengthBound.lean)
-/
@[path]
private lemma length_wordProd_alternatingWord_le
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {i i' : B}
  {n : ℕ}
-- given
  (hM : M i i' ≠ 0) :
-- imply
  cs.length (cs.wordProd (alternatingWord i i' n)) ≤ M i i' := by
-- proof
  induction n using Nat.strongRecOn with
  | _ n ih =>
    if hn : n ≤ M i i' * 2 then
      if hn' : n ≤ M i i' then
        calc
          _ ≤ (alternatingWord i i' n).length := cs.length_wordProd_le _
          _ = n := length_alternatingWord _ _ _
          _ ≤ M i i' := hn'
      else
        rw [cs.prod_alternatingWord_eq_prod_alternatingWord_sub i i' n hn]
        calc
          _ ≤ (alternatingWord i' i (M i i' * 2 - n)).length := cs.length_wordProd_le _
          _ = M i i' * 2 - n := length_alternatingWord _ _ _
          _ ≤ M i i' := by omega
    else
      have hlt : n - M i i' * 2 < n := by omega
      have heq : cs.wordProd (alternatingWord i i' n) =
          cs.wordProd (alternatingWord i i' (n - M i i' * 2)) := by
        have h := wordProd_alternatingWord_periodic (cs := cs) (i := i) (i' := i')
          (n := n - M i i' * 2)
        rwa [Nat.sub_add_cancel (Nat.le_of_not_ge hn)] at h
      rw [heq]
      exact ih (n - M i i' * 2) hlt

end CoxeterSystem

namespace CoxeterSystem

/--
[wordProd_alternatingWord_mul_simple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DihedralLengthBound.lean)
-/
@[path]
private lemma wordProd_alternatingWord_mul_simple
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {i i' : B}
  {n : ℕ} :
-- imply
  cs.wordProd (alternatingWord i i' n) * cs.simple i = cs.wordProd (alternatingWord i' i (n + 1)) := by
-- proof
  rw [alternatingWord_succ i' i n]
  rw [cs.wordProd_concat]

end CoxeterSystem

namespace CoxeterSystem

/--
[wordProd_alternatingWord_mul_same](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DihedralLengthBound.lean)
-/
@[path]
private lemma wordProd_alternatingWord_mul_same
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {i i' : B}
  {n : ℕ} :
-- imply
  cs.wordProd (alternatingWord i' i (n + 1)) * cs.simple i = cs.wordProd (alternatingWord i i' n) := by
-- proof
  have h1 : cs.wordProd (alternatingWord i' i (n + 1)) = cs.wordProd (alternatingWord i i' n) * cs.simple i := by
    rw [alternatingWord_succ i' i n, cs.wordProd_concat]
  rw [h1, mul_assoc, cs.simple_mul_simple_self, mul_one]

end CoxeterSystem

namespace CoxeterSystem

/--
[wordProd_word_in_two_generators](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DihedralLengthBound.lean)
-/
@[path]
private lemma wordProd_word_in_two_generators
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {i i' : B}
  {word : List B}
-- given
  (hmem : ∀ b ∈ word, b = i ∨ b = i') :
-- imply
  ∃ (n : ℕ), cs.wordProd word = cs.wordProd (alternatingWord i i' n) ∨ cs.wordProd word = cs.wordProd (alternatingWord i' i n) := by
-- proof
  induction word using List.reverseRecOn with
  | nil =>
    exact ⟨0, Or.inl (by simp [cs.wordProd_nil, alternatingWord])⟩
  | append_singleton l c ih =>
    have hc : c = i ∨ c = i' := hmem c (by simp)
    have hl : ∀ b ∈ l, b = i ∨ b = i' := fun b hb => hmem b (by simp [hb])
    obtain ⟨n, hn⟩ := ih hl
    rw [cs.wordProd_append, cs.wordProd_singleton]
    obtain hL | hR := hn
    ·
      obtain hci | hci := hc
      ·
        rw [hL, hci]
        exact ⟨n + 1, Or.inr (wordProd_alternatingWord_mul_simple (cs := cs) (i := i) (i' := i') (n := n))⟩
      ·
        rw [hL, hci]
        obtain _ | m := n
        ·
          simp [alternatingWord, cs.wordProd_nil]
          exact ⟨1, Or.inl (by simp [alternatingWord, cs.wordProd_singleton])⟩
        ·
          exact ⟨m, Or.inr (wordProd_alternatingWord_mul_same (cs := cs) (i := i') (i' := i) (n := m))⟩
    ·
      obtain hci | hci := hc
      ·
        rw [hR, hci]
        obtain _ | m := n
        ·
          simp [alternatingWord, cs.wordProd_nil]
          exact ⟨1, Or.inr (by simp [alternatingWord, cs.wordProd_singleton])⟩
        ·
          exact ⟨m, Or.inl (wordProd_alternatingWord_mul_same (cs := cs) (i := i) (i' := i') (n := m))⟩
      ·
        rw [hR, hci]
        exact ⟨n + 1, Or.inl (wordProd_alternatingWord_mul_simple (cs := cs) (i := i') (i' := i) (n := n))⟩

end CoxeterSystem

namespace CoxeterSystem

/--
[length_wordProd_le_M](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DihedralLengthBound.lean)
-/
@[path]
private lemma length_wordProd_le_M
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {i i' : B}
  {word : List B}
-- given
  (hmem : ∀ b ∈ word, b = i ∨ b = i')
  (hM : M i i' ≠ 0) :
-- imply
  cs.length (cs.wordProd word) ≤ M i i' := by
-- proof
  obtain ⟨n, hn⟩ := wordProd_word_in_two_generators (cs := cs) (i := i) (i' := i') (word := word) hmem
  obtain h | h := hn
  ·
    rw [h]
    exact length_wordProd_alternatingWord_le (cs := cs) (i := i) (i' := i') (n := n) hM
  ·
    rw [h]
    have hM' : M i' i ≠ 0 := by rwa [CoxeterMatrix.symmetric]
    calc
      _ ≤ M i' i := length_wordProd_alternatingWord_le (cs := cs) (i := i') (i' := i) (n := n) hM'
      _ = M i i' := CoxeterMatrix.symmetric M i' i

end CoxeterSystem


-- created on 2026-10-23
-- updated on 2026-10-26
