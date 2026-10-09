import sympy.functions.elementary.complexes
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {x : ℕ → ℂ}
-- given
  (h : ∀ i ∈ Finset.range n, x i ∈ Set.range Complex.ofReal) :
-- imply
  ∑ i ∈ Finset.range n, x i ∈ Set.range Complex.ofReal := by
-- proof
  refine ⟨∑ i ∈ Finset.range n, (x i).re, ?_⟩
  push_cast
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain ⟨r, hr⟩ := h i hi
  rw [← hr, Complex.ofReal_re]


-- created on 2023-05-03
