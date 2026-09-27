import sympy.Basic
import sympy.stats.stochastic_process_types
import Lemma.Matrix.Stationary_Pow.of.Stationary
open Matrix


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S]
  {μ : S → ℝ} [StochasticVec μ]
  {P : Matrix S S ℝ} [RowStochastic P]
-- given
  (h₀ : StochasticIrreducible P)
  (h₁ : Stationary μ P) :
-- imply
  ∀ s, 0 < μ s := by
-- proof
  intro j
  obtain ⟨i, hi⟩ : ∃ i, 0 < μ i := by
    by_contra h
    push Not at h
    linarith [StochasticVec.rowsum (x := μ), Finset.sum_nonpos (s := Finset.univ) fun s _ => h s]
  obtain ⟨n, hn⟩ := h₀.irreducible i j
  calc
    _ < μ i * (P ^ n) i j := mul_pos hi hn
    _ ≤ ∑ k, μ k * (P ^ n) k j := by
      apply Finset.single_le_sum (f := fun k => μ k * (P ^ n) k j) _ (Finset.mem_univ i)
      intro k _
      apply mul_nonneg (StochasticVec.nonneg k) ((RowStochastic.stochastic k).nonneg j)
    _ = μ j := congrFun (Stationary_Pow.of.Stationary h₁ (n := n)).stationary j


-- created on 2026-09-22
-- updated on 2026-09-26
