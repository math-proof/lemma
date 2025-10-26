import sympy.sets.sets
import Lemma.Set.In_Range.of.Lt
open Set


@[main]
private lemma main
  {x y : ℕ → α}
-- given
  (h₀ : m < n)
  (h₁ : ∀ i ∈ range n, x i = y i) :
-- imply
  x m = y m := by
-- proof
  -- Apply the universal statement `h₁` to the specific index `m`
  apply h₁ m
  -- Provide the proof that `m < n` (from `h₀`) to satisfy the membership in `range n`
  apply In_Range.of.Lt h₀


@[main]
private lemma is_constant
  {x : ℕ → α}
-- given
  (h₀ : m < n)
  (h₁ : ∀ i ∈ range n, x i = a) :
-- imply
  x m = a := by
-- proof
  let y := fun _ : ℕ => a
  have := main (y := y) h₀ h₁
  simp only [y] at this
  assumption


-- created on 2025-04-26
