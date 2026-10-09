import sympy.concrete.expr_with_limits
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {a b : ℕ → ℝ}
-- given
  (h : ⋃ i ∈ Finset.range n, ({a i} : Set ℝ) = ⋃ i ∈ Finset.range n, ({b i} : Set ℝ)) :
-- imply
  Maxima Set.univ (fun i : Fin n => a i) = Maxima Set.univ (fun i : Fin n => b i) := by
-- proof
  have e : ∀ c : ℕ → ℝ, (fun i : Fin n => c i) '' Set.univ = ⋃ i ∈ Finset.range n, ({c i} : Set ℝ) := by
    intro c
    ext y
    simp only [Set.image_univ, Set.mem_range, Set.mem_iUnion, Set.mem_singleton_iff, Finset.mem_range, exists_prop]
    constructor
    ·
      rintro ⟨i, rfl⟩
      exact ⟨i, i.isLt, rfl⟩
    ·
      rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  show sSup _ = sSup _
  rw [e a, e b, h]


-- created on 2023-11-12
