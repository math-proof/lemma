import sympy.Basic


@[main]
private lemma main
  {s : Set α}
  {y : α}
  {f : α → β}
-- given
  (h : y ∈ s) :
-- imply
  f y ∈ f '' s :=
-- proof
  Set.mem_image_of_mem f h


-- created on 2020-07-29
