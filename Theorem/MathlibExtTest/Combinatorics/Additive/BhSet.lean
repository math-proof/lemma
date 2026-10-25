/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Additive/BhSet.lean -/


import Def.Combinatorics.Additive.BhSet.Part2
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Set.Insert
open AdditiveCombinatorics


/-- The singleton `{7}` is a `B_1`-set over `Nat`: a length-one list over `{7}`
must be `[7]`. -/
example : IsBhSet ({7} : Set Nat) 1 := by
  refine ⟨⟨7, Set.mem_singleton 7⟩, by decide, ?_⟩
  intro l₁ l₂ hm₁ hm₂ hl₁ hl₂ e₁ e₂ hsum
  cases l₁ with
  | nil =>
    exact absurd hl₁ (by decide)
  | cons x xs =>
    cases xs with
    | nil =>
      cases l₂ with
      | nil =>
        exact absurd hl₂ (by decide)
      | cons y ys =>
        cases ys with
        | nil =>
          have hx : x = 7 := Set.mem_singleton_iff.mp (hm₁ x (by simp))
          have hy : y = 7 := Set.mem_singleton_iff.mp (hm₂ y (by simp))
          subst hx
          subst hy
          exact List.Perm.refl _
        | cons z zs =>
          have h2 : 2 ≤ List.length (y :: z :: zs) :=
            Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))
          have hle : 2 ≤ (1 : ℕ) := hl₂ ▸ h2
          exact absurd hle (by decide)
    | cons y ys =>
      have h2 : 2 ≤ List.length (x :: y :: ys) :=
        Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))
      have hle : 2 ≤ (1 : ℕ) := hl₁ ▸ h2
      exact absurd hle (by decide)

/-- Permuted summands with a repeated entry stay permutations. -/
example : ([1, 1, 2] : List Nat).Perm [1, 2, 1] := by
  decide

/-- The permuted repeated-summand lists above have equal nonempty sums. -/
example : sumNE [1, 1, 2] (by decide) = sumNE [1, 2, 1] (by decide) :=
  rfl

/-- The genuine collision `1 + 3 = 2 + 2` shows `{1, 2, 3}` is not a `B_2`-set. -/
example : ¬ IsBhSet ({1, 2, 3} : Set Nat) 2 := by
  intro H
  have m₁ : ∀ x ∈ ([1, 3] : List Nat), x ∈ ({1, 2, 3} : Set Nat) := by
    decide
  have m₂ : ∀ x ∈ ([2, 2] : List Nat), x ∈ ({1, 2, 3} : Set Nat) := by
    decide
  have hperm :=
    H.2.2 [1, 3] [2, 2] m₁ m₂ rfl rfl (by decide) (by decide) rfl
  exact (by decide : ¬ ([1, 3] : List Nat).Perm [2, 2]) hperm

