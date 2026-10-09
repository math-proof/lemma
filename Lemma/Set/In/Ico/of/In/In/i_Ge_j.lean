import sympy.sets.sets
import sympy.Basic


@[path]
private lemma i_in_j
  {a i j n d : ℤ}
-- given
  (h₀ : i ∈ Ico (d + j) n)
  (h₁ : j ∈ Ico a (n - d)) :
-- imply
  i ∈ Ico (a + d) n ∧ j ∈ Ico a (i - d + 1) := by
-- proof
  simp only [Set.mem_Ico] at *
  omega


@[path]
private lemma j_in_i
  {a i j n d : ℤ}
-- given
  (h₀ : j ∈ Ico a (i - d + 1))
  (h₁ : i ∈ Ico (a + d) n) :
-- imply
  i ∈ Ico (d + j) n ∧ j ∈ Ico a (n - d) := by
-- proof
  simp only [Set.mem_Ico] at *
  omega


-- created on 2019-11-05
