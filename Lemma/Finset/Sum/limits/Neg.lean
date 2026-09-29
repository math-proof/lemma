import sympy.Basic


@[main]
private lemma main
  [AddCommMonoid α]
  {n : ℤ}
  {f : ℤ → α} :
-- imply
  ∑ i ∈ Finset.Ico (-n) (n + 1), f i = ∑ i ∈ Finset.Ico (-n) (n + 1), f (-i) := by
-- proof
  apply Finset.sum_nbij' (fun i => -i) (fun i => -i)
  ·
    intro i hi
    simp only [Finset.mem_Ico] at *
    omega
  ·
    intro i hi
    simp only [Finset.mem_Ico] at *
    omega
  ·
    intro i _
    simp
  ·
    intro i _
    simp
  ·
    intro i _
    simp


-- created on 2026-09-27
