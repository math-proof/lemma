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


@[main]
private lemma set
  {S : Set ι}
  {x y : ι → Set β}
-- given
  (h : ∀ i ∈ S, x i = y i) :
-- imply
  ⋃ i ∈ S, x i = ⋃ i ∈ S, y i := by
-- proof
  refine Set.iUnion_congr (fun k => Set.iUnion_congr (fun hk => ?_))
  exact h k hk


-- created on 2025-07-29
