import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {x : Fin n → α}
  {S : Set α}
-- given
  (h : ∀ k, x k ∈ S) :
-- imply
  x ∈ Set.univ.pi (fun _ => S) :=
-- proof
  fun k _ => h k


-- created on 2023-07-02
