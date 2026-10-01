import sympy.sets.sets
import sympy.Basic


@[main]
private lemma relax
  {n : ℕ}
  {a b : ℤ}
  {x : Fin n → ℤ}
-- given
  (h : x ∈ Set.univ.pi fun _ => Set.Ico a b) :
-- imply
  x ∈ Set.univ.pi fun _ => Set.Ico a (b + 1) := by
-- proof
  intro i _
  exact ⟨(h i (Set.mem_univ i)).1, by linarith [(h i (Set.mem_univ i)).2]⟩


-- created on 2026-09-27
