import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {m M U : ℝ}
-- given
  (h₁ : m < M)
  (h₂ : U < max (M ^ 2) (m ^ 2)) :
-- imply
  ∃ x ∈ Set.Ioo m M, x ^ 2 > U := by
-- proof
  have key : ∀ c ∈ closure (Set.Ioo m M), U < c ^ 2 → ∃ x ∈ Set.Ioo m M, x ^ 2 > U := by
    intro c hc hU
    obtain ⟨x, hxV, hxI⟩ := mem_closure_iff.mp hc {y | U < y ^ 2} (isOpen_lt continuous_const (continuous_pow 2)) hU
    exact ⟨x, hxI, hxV⟩
  rw [closure_Ioo h₁.ne] at key
  rcases lt_max_iff.mp h₂ with h₃ | h₃
  · exact key M (Set.right_mem_Icc.mpr h₁.le) h₃
  · exact key m (Set.left_mem_Icc.mpr h₁.le) h₃


-- created on 2019-09-08
