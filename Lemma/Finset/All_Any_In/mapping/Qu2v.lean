import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n u v : ℕ}
-- given
  (_hu : u < n + 1)
  (hv : v < n + 1) :
-- imply
  ∀ x ∈ {x : Fin (n + 1) → ℕ | Finset.univ.image x = Finset.range (n + 1) ∧ x (Fin.last n) = u}, ∃ j : Fin (n + 1), x ∘ Equiv.swap (Fin.last n) j ∈ {x : Fin (n + 1) → ℕ | Finset.univ.image x = Finset.range (n + 1) ∧ x (Fin.last n) = v} := by
-- proof
  intro x hx
  obtain ⟨hi, _⟩ := hx
  have hv' : v ∈ Finset.univ.image x := by
    rw [hi]
    exact Finset.mem_range.mpr hv
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hv'
  refine ⟨j, ?_⟩
  simp only [Set.mem_ofPred_eq]
  constructor
  · rw [← hi, ← Finset.image_image, Finset.image_univ_equiv]
  · rw [Function.comp_apply, Equiv.swap_apply_left, hj]


-- created on 2020-11-01
