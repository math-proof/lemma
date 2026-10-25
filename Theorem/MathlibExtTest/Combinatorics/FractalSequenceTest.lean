/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/FractalSequenceTest.lean -/


import Structure.Combinatorics.FractalSequence
import Lemma.Finset.FractalSequence
import Mathlib.Tactic


namespace MetaMathlibExt

example (X : FractalSequence) (n : ℕ) (h : X.seq n = 0 + 2) :
    ∃ m, m < n ∧ X.seq m = 0 + 1 :=
  X.cond_F2 n 0 h

example (X : FractalSequence) : X.seq (X.pos 0 0) = 0 + 1 :=
  X.pos_sound 0 0

example (X : FractalSequence) (j : ℕ) :
    ∃! k, X.pos 1 j < X.pos 0 k ∧ X.pos 0 k < X.pos 1 (j + 1) :=
  X.cond_F3 0 1 j (by decide)

example (X : FractalSequence) (j k₁ k₂ : ℕ)
    (h₁ : X.pos 1 j < X.pos 0 k₁ ∧ X.pos 0 k₁ < X.pos 1 (j + 1))
    (h₂ : X.pos 1 j < X.pos 0 k₂ ∧ X.pos 0 k₂ < X.pos 1 (j + 1)) :
    k₁ = k₂ := by
  obtain ⟨k, _, huniq⟩ := X.cond_F3 0 1 j (by decide)
  have e₁ := huniq k₁ h₁
  have e₂ := huniq k₂ h₂
  rw [e₁, e₂]

example (X : FractalSequence) : 0 < X.seq 0 :=
  X.seq_pos 0

example (X : FractalSequence) (i : ℕ) : X.pos i 0 < X.pos (i + 1) 0 :=
  X.pos_column_strict 0 (Nat.lt_succ_self i)

end MetaMathlibExt
