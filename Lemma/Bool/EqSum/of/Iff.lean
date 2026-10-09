import sympy.Basic


@[path]
private lemma main
  [AddCommMonoid γ]
  {A : Finset α}
  {B : Finset β}
  {f : α → Finset β}
  {g : β → Finset α}
  {F : α → β → γ}
-- given
  (h : ∀ i j, i ∈ A ∧ j ∈ f i ↔ j ∈ B ∧ i ∈ g j) :
-- imply
  ∑ i ∈ A, ∑ j ∈ f i, F i j = ∑ j ∈ B, ∑ i ∈ g j, F i j :=
-- proof
  Finset.sum_comm' (fun i j => (h i j).trans and_comm)


@[path]
private lemma collapse
  [AddCommMonoid γ]
  {A B : Finset α}
  {f : α → Finset β}
  {k : α → β}
  {F : α → β → γ}
-- given
  (h : ∀ i j, i ∈ A ∧ j ∈ f i ↔ j = k i ∧ i ∈ B) :
-- imply
  ∑ i ∈ A, ∑ j ∈ f i, F i j = ∑ i ∈ B, F i (k i) := by
-- proof
  have hB : B ⊆ A := fun i hi => ((h i (k i)).mpr ⟨rfl, hi⟩).1
  rw [← Finset.sum_subset hB ?_]
  ·
    apply Finset.sum_congr rfl
    intro i hi
    have hf : f i = {k i} := by
      ext j
      simp only [Finset.mem_singleton]
      exact ⟨fun hj => ((h i j).mp ⟨hB hi, hj⟩).1, fun hj => ((h i j).mpr ⟨hj, hi⟩).2⟩
    rw [hf, Finset.sum_singleton]
  ·
    intro i hiA hiB
    apply Finset.sum_eq_zero
    intro j hj
    exact absurd ((h i j).mp ⟨hiA, hj⟩).2 hiB


-- created on 2019-09-13
