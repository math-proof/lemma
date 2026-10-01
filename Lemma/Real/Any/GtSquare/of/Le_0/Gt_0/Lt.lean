import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {m M U : ℝ}
-- given
  (h₀ : m ≤ 0)
  (h₁ : M > 0)
  (h₂ : U < M ^ 2) :
-- imply
  ∃ x ∈ Set.Ioo m M, x ^ 2 > U := by
-- proof
  have hmM : m < M := lt_of_le_of_lt h₀ h₁
  have key : ∀ c ∈ closure (Set.Ioo m M), U < c ^ 2 → ∃ x ∈ Set.Ioo m M, x ^ 2 > U := by
    intro c hc hU
    obtain ⟨x, hxV, hxI⟩ := mem_closure_iff.mp hc {y | U < y ^ 2} (isOpen_lt continuous_const (continuous_pow 2)) hU
    exact ⟨x, hxI, hxV⟩
  rw [closure_Ioo hmM.ne] at key
  exact key M (Set.right_mem_Icc.mpr hmM.le) h₂


-- created on 2026-09-27
