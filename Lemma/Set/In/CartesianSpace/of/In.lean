import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {x : ℕ → α}
  {S : Set α}
-- given
  (h : ∀ i, x i ∈ S) :
-- imply
  (fun i : Fin n => x i) ∈ Set.univ.pi (fun _ => S) :=
-- proof
  fun i _ => h i


-- created on 2021-03-03
