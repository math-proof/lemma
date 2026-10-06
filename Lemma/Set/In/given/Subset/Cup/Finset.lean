import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {S : Set α}
  {x : Fin n → α}
-- given
  (h : x ∈ Set.univ.pi fun _ => S) :
-- imply
  (⋃ i : Fin n, ({x i} : Set α)) ⊆ S := by
-- proof
  intro z hz
  obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hz
  have hzx : z = x i := by simpa using hzi
  rw [hzx]
  exact h i (Set.mem_univ i)


-- created on 2022-09-20
