import sympy.Basic


@[main]
private lemma lhs
  {m : ℕ}
  {x : ℕ → Set α}
  {A : Set α}
-- given
  (h : (⋃ i ∈ Finset.range m, x i) ⊆ A) :
-- imply
  ∀ i ∈ Finset.range m, x i ⊆ A :=
-- proof
  fun i hi _ hy => h (Set.mem_iUnion₂.mpr ⟨i, hi, hy⟩)


-- created on 2020-07-29
