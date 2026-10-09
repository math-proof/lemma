import sympy.sets.sets
import sympy.Basic


@[path]
private lemma i_in_j
  {a i j n d : ℤ}
-- given
  (h₀ : i ∈ Ico (a + d) (j + d))
  (h₁ : j ∈ Ico (a + 1) n) :
-- imply
  i ∈ Ico (a + d) (n - 1 + d) ∧ j ∈ Ico (i - d + 1) n := by
-- proof
  simp only [Set.mem_Ico] at *
  omega


@[path]
private lemma i_in_j.left_close
  {a i j n d : ℤ}
-- given
  (h₀ : i ∈ Ico (a + d) (j + d))
  (h₁ : j ∈ Ico a n) :
-- imply
  i ∈ Ico (a + d) (n + d) ∧ j ∈ Ico (i - d + 1) n := by
-- proof
  simp only [Set.mem_Ico] at *
  omega


@[path]
private lemma j_in_i
  {a i j n d : ℤ}
-- given
  (h₀ : j ∈ Ico (i - d) n)
  (h₁ : i ∈ Ico (a + d) (n + d)) :
-- imply
  i ∈ Ico (a + d) (d + j + 1) ∧ j ∈ Ico a n := by
-- proof
  simp only [Set.mem_Ico] at *
  omega


@[path]
private lemma j_in_i.left_close
  {a i j n d : ℤ}
-- given
  (h₀ : j ∈ Ico (i - d) n)
  (h₁ : i ∈ Ico (a + d) (n + d + 1)) :
-- imply
  i ∈ Ico (a + d) (d + j + 1) ∧ j ∈ Ico (a - 1) n := by
-- proof
  simp only [Set.mem_Ico] at *
  omega


-- created on 2026-09-27
