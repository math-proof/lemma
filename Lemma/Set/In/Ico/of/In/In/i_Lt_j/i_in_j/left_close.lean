import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a i j n d : ℤ}
-- given
  (h₀ : i ∈ Finset.Ico (a + d) (j + d))
  (h₁ : j ∈ Finset.Ico a n) :
-- imply
  i ∈ Finset.Ico (a + d) (n + d) ∧ j ∈ Finset.Ico (i - d + 1) n := by
-- proof
  obtain ⟨hai, hij⟩ := Finset.mem_Ico.mp h₀
  obtain ⟨_, hjn⟩ := Finset.mem_Ico.mp h₁
  constructor
  · exact Finset.mem_Ico.mpr ⟨hai, by omega⟩
  · exact Finset.mem_Ico.mpr ⟨by omega, hjn⟩


-- created on 2020-03-06
