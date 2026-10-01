import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {n : ℕ}
  {x : Fin n → ℤ}
  {S : Set ℤ}
-- given
  (h : ↑(Finset.univ.image x) ⊆ S) :
-- imply
  x ∈ Set.univ.pi (fun _ => S) := by
-- proof
  exact fun i _ => h (Finset.mem_coe.mpr (Finset.mem_image_of_mem x (Finset.mem_univ i)))


-- created on 2026-09-27
