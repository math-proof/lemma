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
    ∑ c ∈ Finset.Icc a b, ∑ v ∈ Fintype.piFinset (fun _ : Fin m => Finset.Icc a b),
      (if g (Fin.cons c v) > 0 then f (Fin.cons c v) else 0) := by
-- proof
  rw [← Finset.sum_product' (f := fun c v => if g (Fin.cons c v) > 0 then f (Fin.cons c v) else 0)]
  symm
  refine Finset.sum_nbij' (fun p : ℤ × (Fin m → ℤ) => (Fin.cons p.1 p.2 : Fin (m + 1) → ℤ))
    (fun w => (w 0, Fin.tail w)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_product, Fintype.mem_piFinset] at hp
    rw [Fintype.mem_piFinset]
    intro i
    cases i using Fin.cases with
    | zero =>
      simpa using hp.1
    | succ j =>
      simpa using hp.2 j
  · intro w hw
    rw [Fintype.mem_piFinset] at hw
    rw [Finset.mem_product, Fintype.mem_piFinset]
    exact ⟨hw 0, fun j => hw j.succ⟩
  · intro p _
    simp
  · intro w _
    exact Fin.cons_self_tail w
  · intro p _
    rfl


-- created on 2020-03-18
