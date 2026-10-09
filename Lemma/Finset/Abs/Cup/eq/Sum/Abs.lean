import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pi
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma permutation.nonoverlapping
  {n : ℕ} :
-- imply
  (⋃ t ∈ Finset.range (n + 1), {x : Fin (n + 1) → ℕ | Finset.univ.image x = Finset.range (n + 1) ∧ x (Fin.last n) = t}).ncard =
    ∑ t ∈ Finset.range (n + 1), ({x : Fin (n + 1) → ℕ | Finset.univ.image x = Finset.range (n + 1) ∧ x (Fin.last n) = t}).ncard := by
-- proof
  set F := (Fintype.piFinset fun _ : Fin (n + 1) => Finset.range (n + 1)).filter
    (fun x => Finset.univ.image x = Finset.range (n + 1)) with hF
  have mem : ∀ x : Fin (n + 1) → ℕ, x ∈ F ↔ Finset.univ.image x = Finset.range (n + 1) := by
    intro x
    rw [hF, Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun h => h.2, fun h => ⟨fun i => ?_, h⟩⟩
    rw [← h]
    exact Finset.mem_image_of_mem x (Finset.mem_univ i)
  have hQ : ∀ t, {x : Fin (n + 1) → ℕ | Finset.univ.image x = Finset.range (n + 1) ∧ x (Fin.last n) = t} = ↑(F.filter (fun x => x (Fin.last n) = t)) := by
    intro t
    ext x
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem]
  have hU : (⋃ t ∈ Finset.range (n + 1), {x : Fin (n + 1) → ℕ | Finset.univ.image x = Finset.range (n + 1) ∧ x (Fin.last n) = t}) = ↑F := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_coe, mem, exists_prop]
    constructor
    · rintro ⟨t, _, h, _⟩
      exact h
    · intro h
      refine ⟨x (Fin.last n), ?_, h, rfl⟩
      rw [← h]
      exact Finset.mem_image_of_mem x (Finset.mem_univ _)
  rw [hU, Set.ncard_coe_finset]
  simp only [hQ, Set.ncard_coe_finset]
  exact Finset.card_eq_sum_card_fiberwise (fun x hx => by
    rw [← (mem x).mp hx]
    exact Finset.mem_image_of_mem x (Finset.mem_univ _))


-- created on 2026-09-27
