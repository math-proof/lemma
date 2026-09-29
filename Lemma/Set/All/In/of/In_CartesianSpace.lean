import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n m : ℕ}
  {x : Fin n → ℤ}
-- given
  (h : x ∈ Set.univ.pi (fun _ => Set.Ico (0 : ℤ) m)) :
-- imply
  ∀ i, x i ∈ Set.Ico (0 : ℤ) m := by
-- proof
  exact fun i => h i (Set.mem_univ i)


-- created on 2026-09-27
