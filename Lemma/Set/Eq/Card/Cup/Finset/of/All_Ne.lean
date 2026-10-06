import sympy.Basic


@[main]
private lemma main
  [DecidableEq α]
  {n : ℕ}
  {x : ℕ → α}
-- given
  (h : ∀ i < n, ∀ j < i, x i ≠ x j) :
-- imply
  (Finset.biUnion (Finset.range n) fun i => ({x i} : Finset α)).card = n := by
-- proof
  have hinj : Set.InjOn x (Finset.range n) := by
    intro i hi j hj heq
    if hlt : i < j then
      exact False.elim (h j (Finset.mem_range.mp hj) i hlt heq.symm)
    else if hgt : j < i then
      exact False.elim (h i (Finset.mem_range.mp hi) j hgt heq)
    else
      omega
  have hbi : Finset.biUnion (Finset.range n) (fun i : ℕ => ({x i} : Finset α)) =
      Finset.image x (Finset.range n) := by
    ext y
    simp only [Finset.mem_biUnion, Finset.mem_singleton, Finset.mem_image]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, rfl⟩
  rw [hbi, Finset.card_image_of_injOn hinj, Finset.card_range]


-- created on 2021-01-14
