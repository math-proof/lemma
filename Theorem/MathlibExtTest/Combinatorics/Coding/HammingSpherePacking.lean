/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Coding/HammingSpherePacking.lean -/


import Lemma.Finset.Coding.HammingSpherePacking
open MathlibExt.Combinatorics.Coding.HammingSpherePacking


-- Generic public API: the exact former Wanted signature.
example {α : Type*} [Fintype α] [DecidableEq α] {n t : ℕ}
    (C : Finset (Fin n → α))
    (hα : 2 ≤ Fintype.card α)
    (hDist : ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ →
      2 * t + 1 ≤ hammingDist c₁ c₂) :
    C.card * (∑ i ∈ Finset.range (t + 1),
      n.choose i * (Fintype.card α - 1) ^ i) ≤ (Fintype.card α) ^ n :=
  hamming_sphere_packing_bound C hα hDist

-- Empty codes satisfy the bound vacuously.
example : (∅ : Finset (Fin 2 → Fin 2)).card *
    (∑ i ∈ Finset.range (0 + 1),
      (2).choose i * (Fintype.card (Fin 2) - 1) ^ i) ≤
    (Fintype.card (Fin 2)) ^ 2 := by
  refine hamming_sphere_packing_bound _ (by decide) ?_
  intro c₁ hc₁ c₂ _ _
  exact absurd hc₁ (Finset.notMem_empty c₁)

-- Singleton codes fit well below the bound.
example (c : Fin 3 → Fin 2) :
    ({c} : Finset (Fin 3 → Fin 2)).card *
    (∑ i ∈ Finset.range (1 + 1),
      (3).choose i * (Fintype.card (Fin 2) - 1) ^ i) ≤
    (Fintype.card (Fin 2)) ^ 3 := by
  refine hamming_sphere_packing_bound _ (by decide) ?_
  intro c₁ hc₁ c₂ hc₂ hne
  rw [Finset.mem_singleton] at hc₁ hc₂
  exact absurd (hc₁.trans hc₂.symm) hne

-- Boundary `t = 0`: the whole space meets the `q ^ n` bound.
example : (Finset.univ : Finset (Fin 2 → Fin 2)).card *
    (∑ i ∈ Finset.range (0 + 1),
      (2).choose i * (Fintype.card (Fin 2) - 1) ^ i) ≤
    (Fintype.card (Fin 2)) ^ 2 := by
  refine hamming_sphere_packing_bound _ (by decide) ?_
  intro c₁ _ c₂ _ hne
  have hpos : 0 < hammingDist c₁ c₂ := hammingDist_pos.mpr hne
  exact hpos

-- Tight boundary case: the binary length-3 repetition code corrects one error
-- and meets the bound with equality (`2 * 4 = 8`).
example : ({fun _ => (0 : Fin 2), fun _ => (1 : Fin 2)} :
    Finset (Fin 3 → Fin 2)).card *
    (∑ i ∈ Finset.range (1 + 1),
      (3).choose i * (Fintype.card (Fin 2) - 1) ^ i) ≤
    (Fintype.card (Fin 2)) ^ 3 := by
  refine hamming_sphere_packing_bound _ (by decide) ?_
  intro c₁ hc₁ c₂ hc₂ hne
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc₁ hc₂
  rcases hc₁ with rfl | rfl <;> rcases hc₂ with rfl | rfl
  · exact absurd rfl hne
  · decide
  · decide
  · exact absurd rfl hne

-- Numeric value of the volume sum in the tight case above.
example : ∑ i ∈ Finset.range (1 + 1),
    (3).choose i * (Fintype.card (Fin 2) - 1) ^ i = 4 := by decide

example : (Fintype.card (Fin 2)) ^ 3 = 8 := by decide

