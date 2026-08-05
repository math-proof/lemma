import sympy.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
open Int


@[main]
private lemma main
  [AddCommMonoid α]
  (a b d : ℤ)
  (f : ℤ → α) :
-- imply
  ∑ n ∈ Finset.Ico a b, f n = ∑ n ∈ Finset.Ico (a - d) (b - d), f (n + d) := by
-- proof
  apply Finset.sum_bij (fun m _ => m - d)
  · intro m hm
    simp only [Finset.mem_Ico] at hm ⊢
    rcases hm with ⟨h₁, h₂⟩
    exact ⟨by omega, by omega⟩
  · intro m₁ _ m₂ _ h
    omega
  · intro n hn
    refine ⟨n + d, ?_, by omega⟩
    simp only [Finset.mem_Ico] at hn ⊢
    rcases hn with ⟨h₁, h₂⟩
    exact ⟨by omega, by omega⟩
  · intro m hm
    simp


-- created on 2018-04-28
