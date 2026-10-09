import Mathlib.Algebra.Order.BigOperators.Group.Finset
import sympy.concrete.expr_with_limits
import Mathlib.Analysis.InnerProductSpace.PiL2
import sympy.Basic


@[path]
private lemma kmeans.w_quote
  {M k d : ℕ} [NeZero k]
  {w w' : ℕ → Finset ℕ}
  {x : ℕ → EuclideanSpace ℝ (Fin d)}
  {i j : ℕ}
-- given
  (_ : ∑ i ∈ Finset.range k, (w i).card = M)
  (_ : (Finset.range k).biUnion w = Finset.range M)
  (h₂ : ∀ i, w' i = (Finset.range M).filter fun j => ((ArgMin Set.univ (fun i' : Fin k => ‖x j - (((w i').card : ℝ)⁻¹ • ∑ j' ∈ w i', x j')‖) : Fin k) : ℕ) = i) :
-- imply
  (j ∈ w' i ∧ i < k) ↔ (i = ((ArgMin Set.univ (fun i' : Fin k => ‖x j - (((w i').card : ℝ)⁻¹ • ∑ j' ∈ w i', x j')‖) : Fin k) : ℕ) ∧ j < M) := by
-- proof
  rw [h₂]
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  ·
    rintro ⟨⟨hj, e⟩, _⟩
    exact ⟨e.symm, hj⟩
  ·
    rintro ⟨e, hj⟩
    exact ⟨⟨hj, e.symm⟩, by rw [e]; exact Fin.isLt _⟩


-- created on 2026-09-27
