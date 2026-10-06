import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {a b : ℤ}
  {x : Fin n → ℤ}
-- given
  (h : x ∈ Set.univ.pi fun _ => Set.Icc a b) :
-- imply
  x ∈ Set.univ.pi fun _ => Set.Icc (a - 1) b := by
-- proof
  intro i _
  exact ⟨by linarith [(h i (Set.mem_univ i)).1], (h i (Set.mem_univ i)).2⟩


-- created on 2023-08-20
