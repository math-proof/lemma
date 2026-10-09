import sympy.concrete.expr_with_limits
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ}
  {c : ℝ}
-- given
  (h : c ∈ ⋃ i ∈ Finset.range n, ({x i} : Set ℝ)) :
-- imply
  c ≤ Maxima Set.univ (fun i : Fin n => x i) := by
-- proof
  obtain ⟨i, hi, hc⟩ := Set.mem_iUnion₂.mp h
  rw [Set.mem_singleton_iff] at hc
  subst hc
  exact le_csSup (Set.finite_univ.image _).bddAbove ⟨⟨i, Finset.mem_range.mp hi⟩, Set.mem_univ _, rfl⟩


-- created on 2023-11-12
