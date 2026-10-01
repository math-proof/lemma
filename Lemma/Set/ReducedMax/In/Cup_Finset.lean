import sympy.concrete.expr_with_limits
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  [NeZero n]
  {x : ℕ → ℝ} :
-- imply
  Maxima Set.univ (fun i : Fin n => x i) ∈ ⋃ i ∈ Finset.range n, ({x i} : Set ℝ) := by
-- proof
  obtain ⟨i, _, e⟩ := (Set.univ_nonempty.image (fun i : Fin n => x i)).csSup_mem (Set.finite_univ.image _)
  exact Set.mem_iUnion₂.mpr ⟨i, Finset.mem_range.mpr i.isLt, Set.mem_singleton_iff.mpr e.symm⟩


-- created on 2023-11-12
