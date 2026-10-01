import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Fin
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {m : ℕ}
  {a b : ℤ}
  {f g : (Fin (m + 1) → ℤ) → ℝ} :
-- imply
  ∑ w ∈ Fintype.piFinset (fun _ : Fin (m + 1) => Finset.Icc a b), (if g w > 0 then f w else 0) =
    ∑ v ∈ Fintype.piFinset (fun _ : Fin m => Finset.Icc a b), ∑ c ∈ Finset.Icc a b,
      (if g (Fin.snoc v c) > 0 then f (Fin.snoc v c) else 0) := by
-- proof
  rw [← Finset.sum_product' (f := fun v c => if g (Fin.snoc v c) > 0 then f (Fin.snoc v c) else 0)]
  symm
  refine Finset.sum_nbij' (fun p : (Fin m → ℤ) × ℤ => (Fin.snoc p.1 p.2 : Fin (m + 1) → ℤ))
    (fun w => (Fin.init w, w (Fin.last m))) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_product, Fintype.mem_piFinset] at hp
    rw [Fintype.mem_piFinset]
    intro i
    cases i using Fin.lastCases with
    | last =>
      simpa using hp.2
    | cast j =>
      simpa using hp.1 j
  · intro w hw
    rw [Fintype.mem_piFinset] at hw
    rw [Finset.mem_product, Fintype.mem_piFinset]
    exact ⟨fun j => hw j.castSucc, hw (Fin.last m)⟩
  · intro p _
    simp
  · intro w _
    exact Fin.snoc_init_self w
  · intro p _
    rfl


-- created on 2023-08-20
