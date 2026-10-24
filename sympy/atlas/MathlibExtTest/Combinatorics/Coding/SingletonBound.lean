/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Coding/SingletonBound.lean -/


import Lemma.Finset.Coding.SingletonBound

open MathlibExt.Combinatorics.Coding.SingletonBound

-- Generic public API: the bound applies to any code meeting the hypotheses.
example {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n d : ℕ}
    (C : Finset (Fin n → α)) (hd1 : 1 ≤ d) (hd2 : d ≤ n)
    (hDist : ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → d ≤ hammingDist c₁ c₂) :
    C.card ≤ (Fintype.card α) ^ (n - d + 1) :=
  singleton_bound C hd1 hd2 hDist

-- Empty codes satisfy every bound vacuously.
example : (∅ : Finset (Fin 2 → Fin 2)).card ≤
    (Fintype.card (Fin 2)) ^ (2 - 2 + 1) := by
  refine singleton_bound _ (by norm_num) (by norm_num) ?_
  intro c₁ hc₁ c₂ _ _
  exact absurd hc₁ (Finset.notMem_empty c₁)

-- Singleton codes fit well below the bound.
example (c : Fin 3 → Fin 2) :
    ({c} : Finset (Fin 3 → Fin 2)).card ≤
      (Fintype.card (Fin 2)) ^ (3 - 2 + 1) := by
  refine singleton_bound _ (by norm_num) (by norm_num) ?_
  intro c₁ hc₁ c₂ hc₂ hne
  rw [Finset.mem_singleton] at hc₁ hc₂
  exact absurd (hc₁.trans hc₂.symm) hne

-- Boundary `d = 1`: the whole space meets the `q ^ n` bound.
example : (Finset.univ : Finset (Fin 2 → Fin 2)).card ≤
    (Fintype.card (Fin 2)) ^ (2 - 1 + 1) := by
  refine singleton_bound _ (by norm_num) (by norm_num) ?_
  intro c₁ _ c₂ _ hne
  have hpos : 0 < hammingDist c₁ c₂ := by
    rw [hammingDist_pos]
    exact hne
  exact hpos

-- Boundary `d = n`: the binary repetition code attains the `q` bound.
example : ({fun _ => (0 : Fin 2), fun _ => (1 : Fin 2)} :
    Finset (Fin 3 → Fin 2)).card ≤
      (Fintype.card (Fin 2)) ^ (3 - 3 + 1) := by
  refine singleton_bound _ (by norm_num) (by norm_num) ?_
  intro c₁ hc₁ c₂ hc₂ hne
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc₁ hc₂
  rcases hc₁ with rfl | rfl <;> rcases hc₂ with rfl | rfl
  · exact absurd rfl hne
  · decide
  · decide
  · exact absurd rfl hne

-- Numeric boundary values of the exponent and alphabet size.
example : (Fintype.card (Fin 2)) ^ (3 - 3 + 1) = 2 := by decide

example : (Fintype.card (Fin 2)) ^ (2 - 1 + 1) = 4 := by decide
