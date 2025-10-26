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
  ∀ i ∈ range m, x i = y i := by
-- proof
  -- Introduce an arbitrary element `i` in the range up to `m`
  intro i hi
  -- Simplify the membership condition `hi` to `i < m`
  simp at hi
  -- Use linear arithmetic to prove `i < n` from `i < m` and `m < n`
  have hi' : i < n := by linarith [h₀, hi]
  -- Apply the universal equality hypothesis `h₁` to `i` and the proof `i < n`
  have h_Mem := In_Range.of.Lt hi'
  exact h₁ i h_Mem


@[main]
private lemma is_constant
  {x : ℕ → α}
  {a : α}
-- given
  (h₀ : m<n)
  (h₁ : ∀ i ∈ range n, x i = a) :
-- imply
  ∀ i ∈ range m, x i = a := by
-- proof
  let y := fun _ : ℕ => a
  have := main (y := y) h₀ h₁
  simp only [y] at this
  assumption


-- created on 2025-04-26
