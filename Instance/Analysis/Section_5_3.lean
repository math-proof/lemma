module

public import Mathlib
public import Theorem.Analysis.Section_5_2.Part2
public import Mathlib.Algebra.Group.MinimalAxioms
public import Theorem.Analysis.Section_5_3.Part2

@[expose] public section

/-!
# Analysis I, Section 5.3: The construction of the real numbers

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Notion of a formal limit of a Cauchy sequence.
- Construction of a real number type `Chapter5.Real`.
- Basic arithmetic operations and properties.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/


namespace Chapter5

instance CauchySequence.instCoeFun : CoeFun CauchySequence (fun _ ↦ ℕ → ℚ) where
  coe a n := a.toSequence.seq (n:ℤ)


instance CauchySequence.instSetoid : Setoid CauchySequence where
  r := fun a b ↦ Sequence.Equiv a b
  iseqv := {
    refl := by
      intro a ε hε
      refine ⟨(0 : ℤ), ?_⟩
      intro n _ _
      rw [Section_4_3.close_iff]
      simp
      exact le_of_lt hε
    symm := by
      intro a b hab ε hε
      obtain ⟨N, hN⟩ := hab ε hε
      refine ⟨N, ?_⟩
      intro n hna hnb
      exact (Section_4_3.close_symm ε _ _).mp (hN n hnb hna)
    trans := by
      intro a b c hab hbc ε hε
      have hε2 : 0 < ε / 2 := half_pos hε
      obtain ⟨N₁, h₁⟩ := hab (ε / 2) hε2
      obtain ⟨N₂, h₂⟩ := hbc (ε / 2) hε2
      refine ⟨max N₁ N₂, ?_⟩
      intro n hna hnc
      have n₀_from (x : ℕ → ℚ) (N : ℤ) :
          ((Sequence.ofNatFun x).from N).n₀ = max 0 N := rfl
      have hn_max : n ≥ max 0 (max N₁ N₂) := by
        rwa [n₀_from (a : ℕ → ℚ) (max N₁ N₂)] at hna
      have hn1 : n ≥ max 0 N₁ := by omega
      have hn2 : n ≥ max 0 N₂ := by omega
      have seq_from (x : ℕ → ℚ) (N : ℤ) (hn : n ≥ max 0 N) :
          ((Sequence.ofNatFun x).from N).seq n = (Sequence.ofNatFun x).seq n := by
        have hx0 : (Sequence.ofNatFun x).n₀ = 0 := rfl
        have hcond : n ≥ max (Sequence.ofNatFun x).n₀ N := by
          rwa [hx0]
        dsimp [Sequence.from, Sequence.mk']
        split_ifs
        rfl
      have h1' := h₁ n
        (by rwa [n₀_from (a : ℕ → ℚ) N₁])
        (by rwa [n₀_from (b : ℕ → ℚ) N₁])
      have h2' := h₂ n
        (by rwa [n₀_from (b : ℕ → ℚ) N₂])
        (by rwa [n₀_from (c : ℕ → ℚ) N₂])
      rw [Section_4_3.close_iff] at h1' h2' ⊢
      rw [seq_from (a : ℕ → ℚ) (max N₁ N₂) hn_max,
          seq_from (c : ℕ → ℚ) (max N₁ N₂) hn_max]
      rw [seq_from (a : ℕ → ℚ) N₁ hn1, seq_from (b : ℕ → ℚ) N₁ hn1] at h1'
      rw [seq_from (b : ℕ → ℚ) N₂ hn2, seq_from (c : ℕ → ℚ) N₂ hn2] at h2'
      set sa := (Sequence.ofNatFun (a : ℕ → ℚ)).seq n
      set sb := (Sequence.ofNatFun (b : ℕ → ℚ)).seq n
      set sc := (Sequence.ofNatFun (c : ℕ → ℚ)).seq n
      calc
        |sa - sc| ≤ |sa - sb| + |sb - sc| := abs_sub_le sa sb sc
        _ ≤ ε / 2 + ε / 2 := add_le_add h1' h2'
        _ = ε := add_halves ε
  }

end Chapter5
