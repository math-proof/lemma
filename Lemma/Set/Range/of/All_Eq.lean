import sympy.Basic


@[main]
private lemma main
  {ι : Sort u}
  {x y : ι → α}
-- given
  (h : ∀ i : ι, x i = y i) :
-- imply
  Set.range x = Set.range y := by
-- proof
  apply congrArg Set.range
  apply funext h


@[main]
private lemma set
  {S : Set ι}
  {x y : ι → α}
-- given
  (h : ∀ i ∈ S, x i = y i) :
-- imply
  S.image x = S.image y := by
-- proof
  apply Set.image_congr
  intro i hi
  apply h
  assumption


-- created on 2020-07-23
-- updated on 2026-09-08
