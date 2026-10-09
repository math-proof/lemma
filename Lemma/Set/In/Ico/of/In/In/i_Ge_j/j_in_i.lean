import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a i j n d : ℤ}
-- given
  (h₀ : j ∈ Finset.Ico a (i - d + 1))
  (h₁ : i ∈ Finset.Ico (a + d) n) :
-- imply
  i ∈ Finset.Ico (d + j) n ∧ j ∈ Finset.Ico a (n - d) := by
-- proof
  obtain ⟨haj, hji⟩ := Finset.mem_Ico.mp h₀
  obtain ⟨_, hin⟩ := Finset.mem_Ico.mp h₁
  constructor
  · exact Finset.mem_Ico.mpr ⟨by omega, hin⟩
  · exact Finset.mem_Ico.mpr ⟨haj, by omega⟩


-- created on 2019-11-05
