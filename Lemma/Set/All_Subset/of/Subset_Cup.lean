import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {x : ℕ → Set α}
  {A : Set α}
-- given
  (h : (⋃ i ∈ Finset.range n, x i) ⊆ A) :
-- imply
  ∀ i ∈ Finset.range n, x i ⊆ A :=
-- proof
  fun i hi _ hy => h (Set.mem_iUnion₂.mpr ⟨i, hi, hy⟩)


-- created on 2026-09-27
