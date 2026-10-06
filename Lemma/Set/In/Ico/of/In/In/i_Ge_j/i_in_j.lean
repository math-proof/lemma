import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a i j n d : ℤ}
-- given
  (h₀ : i ∈ Finset.Ico (d + j) n)
  (h₁ : j ∈ Finset.Ico a (n - d)) :
-- imply
  i ∈ Finset.Ico (a + d) n ∧ j ∈ Finset.Ico a (i - d + 1) := by
-- proof
  obtain ⟨hij, hin⟩ := Finset.mem_Ico.mp h₀
  obtain ⟨haj, _⟩ := Finset.mem_Ico.mp h₁
  constructor
  · exact Finset.mem_Ico.mpr ⟨by omega, hin⟩
  · exact Finset.mem_Ico.mpr ⟨haj, by omega⟩


-- created on 2019-11-05
