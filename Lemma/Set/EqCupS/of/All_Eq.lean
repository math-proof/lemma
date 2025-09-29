import sympy.Basic


@[main]
private lemma main
  {ι : Sort u}
  {x y : ι → Set β}
-- given
  (h : ∀ i : ι, x i = y i) :
-- imply
  ⋃ i : ι, x i = ⋃ i : ι, y i :=
-- proof
  Set.iUnion_congr h


-- created on 2025-07-29
