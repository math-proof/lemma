import Lemma.Basic


@[main]
private lemma main
  {n : ℕ} :
-- imply
  ∀ i ∈ List.range n, i < n := by
-- proof
  intro i
  rw [List.mem_range (n := n) (m := i)]
  simp


-- created on 2025-05-03
