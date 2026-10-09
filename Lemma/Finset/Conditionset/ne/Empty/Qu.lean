import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n u : ℕ}
-- given
  (h : u < n + 1) :
-- imply
  {x : Fin (n + 1) → ℕ | Finset.univ.image x = Finset.range (n + 1) ∧ x (Fin.last n) = u} ≠ ∅ := by
-- proof
  have himg : Finset.univ.image (fun i : Fin (n + 1) => (i : ℕ)) = Finset.range (n + 1) := by
    ext y
    rw [Finset.mem_image, Finset.mem_range]
    exact ⟨fun ⟨a, _, e⟩ => e ▸ a.isLt, fun hy => ⟨⟨y, hy⟩, Finset.mem_univ _, rfl⟩⟩
  apply Set.nonempty_iff_ne_empty.mp
  refine ⟨(fun i : Fin (n + 1) => (i : ℕ)) ∘ Equiv.swap (Fin.last n) ⟨u, h⟩, ?_, ?_⟩
  · rw [← Finset.image_image, Finset.image_univ_equiv, himg]
  · rw [Function.comp_apply, Equiv.swap_apply_left]


-- created on 2020-11-07
