import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a i j n d : ℤ}
-- given
  (h₀ : j ∈ Finset.Ico (i - d + 1) n)
  (h₁ : i ∈ Finset.Ico (a + d) (d + n)) :
-- imply
  i ∈ Finset.Ico (a + d) (d + j + 1) ∧ j ∈ Finset.Ico (a - 1) n := by
-- proof
  obtain ⟨hij, hjn⟩ := Finset.mem_Ico.mp h₀
  obtain ⟨hai, _⟩ := Finset.mem_Ico.mp h₁
  constructor
  · exact Finset.mem_Ico.mpr ⟨hai, by omega⟩
  · exact Finset.mem_Ico.mpr ⟨by omega, hjn⟩


-- created on 2020-03-06
