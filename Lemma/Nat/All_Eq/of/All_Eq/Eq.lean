import Lemma.Set.In_Range.ou.Eq.of.In_Range
open Set


@[path]
private lemma main
  {x y : ℕ → α}
-- given
  (h₀ : x n = y n)
  (h₁ : ∀ i < n, x i = y i) :
-- imply
  ∀ i < (n + 1), x i = y i := by
-- proof
  intro i hi
  try simp only [← Finset.mem_range] at *
  obtain h | h := In_Range.ou.Eq.of.In_Range hi <;>
    simp_all


@[path]
private lemma is_constant
  {x : ℕ → α}
  {a : α}
-- given
  (h₀ : x n = a)
  (h₁ : ∀ i < n, x i = a) :
-- imply
  ∀ i < (n + 1), x i = a := by
-- proof
  let y := fun _ : ℕ => a
  have := main (y := y) h₀ h₁
  simp only [y] at this
  assumption


-- created on 2025-04-26
