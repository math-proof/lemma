import sympy.Basic


@[main]
private lemma main
  {A : Set α}
  {x y : α}
-- given
  (h : {x, y} ⊆ A) :
-- imply
  x ∈ A :=
-- proof
  h (Set.mem_insert x {y})


@[main]
private lemma given
  {s : Set α}
  {e : α}
-- given
  (h : {e} ⊆ s) :
-- imply
  e ∈ s :=
-- proof
  h (Set.mem_singleton e)


-- created on 2020-07-27
