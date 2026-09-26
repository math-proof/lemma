import Mathlib.Order.Filter.Basic
import Mathlib.Algebra.BigOperators.Pi
import sympy.Basic
open Filter


@[main]
private lemma main
  [AddCommGroup β]
  {l : Filter α}
  {s : Finset ι}
  {f g : ι → α → β}
-- given
  (h₀ : ∀ i ∈ s, f i =ᶠ[l] g i) :
-- imply
  ∑ i ∈ s, f i =ᶠ[l] ∑ i ∈ s, g i := by
-- proof
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    simp only [Finset.sum_cons]
    exact (h₀ a (by simp)).add (ih fun i hi => h₀ i (by simp [hi]))


-- created on 2026-09-26