import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {x : ℕ → ℤ}
  {S : Set ℤ}
-- given
  (h : ∀ i < n, x i ∈ S) :
-- imply
  (fun i : Fin n => x i) ∈ Set.univ.pi (fun _ => S) := by
-- proof
  exact fun i _ => h i i.isLt


-- created on 2022-09-20
