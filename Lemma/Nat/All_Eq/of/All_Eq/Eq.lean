import sympy.sets.sets
import Lemma.Set.In_Range.ou.Eq.of.In_Range
open Set


@[main]
private lemma main
  {x y : ℕ → α}
-- given
  (h₀ : x n = y n)
  (h₁ : ∀ i ∈ range n, x i = y i) :
-- imply
  ∀ i ∈ range (n + 1), x i = y i := by
-- proof
  intro i hi
  obtain h | h := In_Range.ou.Eq.of.In_Range hi <;>
    simp_all


@[main]
private lemma is_constant
  {x : ℕ → α}
  {a : α}
-- given
  (h₀ : x n = a)
  (h₁ : ∀ i ∈ range n, x i = a) :
-- imply
  ∀ i ∈ range (n + 1), x i = a := by
-- proof
  let y := fun _ : ℕ => a
  have := main (y := y) h₀ h₁
  simp only [y] at this
  assumption


-- created on 2025-04-26
