import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
-- given
  (_h : n > 0) :
-- imply
  {x : Fin n → ℕ | Finset.univ.image x = Finset.range n} ≠ ∅ := by
-- proof
  apply Set.nonempty_iff_ne_empty.mp
  refine ⟨fun i => (i : ℕ), ?_⟩
  show Finset.univ.image (fun i : Fin n => (i : ℕ)) = Finset.range n
  ext y
  rw [Finset.mem_image, Finset.mem_range]
  exact ⟨fun ⟨a, _, e⟩ => e ▸ a.isLt, fun h => ⟨⟨y, h⟩, Finset.mem_univ _, rfl⟩⟩


-- created on 2020-11-06
