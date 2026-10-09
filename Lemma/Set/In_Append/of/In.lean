import sympy.Basic


@[path]
private lemma main
  {a : List α}
-- given
  (h : x ∈ a)
  (b : List α) :
-- imply
  x ∈ b ++ a :=
-- proof
  List.mem_append_right b h


@[path]
private lemma left
  {a : List α}
-- given
  (h : x ∈ a)
  (b : List α) :
-- imply
  x ∈ a ++ b :=
-- proof
  List.mem_append_left b h


-- created on 2025-07-08
