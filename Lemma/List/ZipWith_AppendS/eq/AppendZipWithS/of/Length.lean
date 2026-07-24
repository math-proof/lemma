import sympy.Basic


@[main]
private lemma main
  {a : List α}
  {b : List β}
  -- given
  (h : a.length = b.length)
  (f : α → β → γ)
  (a' : List α)
  (b' : List β) :
-- imply
  List.zipWith f (a ++ a') (b ++ b') = List.zipWith f a b ++ List.zipWith f a' b' :=
-- proof
  List.zipWith_append h


-- created on 2026-01-03
