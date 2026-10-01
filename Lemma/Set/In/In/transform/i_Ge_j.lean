import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a i j n d : ℤ} :
-- imply
  i ∈ Ico (d + j) n ∧ j ∈ Ico a (n - d) ↔ j ∈ Ico a (i - d + 1) ∧ i ∈ Ico (a + d) n := by
-- proof
  simp only [Set.mem_Ico]
  omega


-- created on 2026-09-27
