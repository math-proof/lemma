import sympy.Basic


@[main]
private lemma main
  [AddCommMonoid α]
  {a b c : ℤ}
  {f : ℤ → α} :
-- imply
  ∑ i ∈ Finset.Ico a b, f i = ∑ i ∈ Finset.Ico (c - b) (c - a), f (c - i - 1) := by
-- proof
  apply Finset.sum_nbij' (fun i => c - i - 1) (fun i => c - i - 1)
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
    omega
  ·
    intro i _
    omega
  ·
    intro i _
    congr 1
    omega


-- created on 2020-03-19
