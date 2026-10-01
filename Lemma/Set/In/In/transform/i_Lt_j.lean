import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a i j n d : ℤ} :
-- imply
  i ∈ Ico (a + d) (j + d) ∧ j ∈ Ico (a + 1) n ↔ i ∈ Ico (a + d) (n - 1 + d) ∧ j ∈ Ico (i - d + 1) n := by
-- proof
  simp only [Set.mem_Ico]
  omega


@[main]
private lemma left_close
  {a i j n d : ℤ} :
-- imply
  i ∈ Ico (a + d) (j + d) ∧ j ∈ Ico a n ↔ i ∈ Ico (a + d) (n + d) ∧ j ∈ Ico (i - d + 1) n := by
-- proof
  simp only [Set.mem_Ico]
  omega


-- created on 2026-09-27
