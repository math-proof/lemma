import sympy.Basic


@[main]
private lemma main
-- given
  (v : List α)
  (i : ℕ) :
-- imply
  (v.rotate i).length = v.length :=
-- proof
  List.length_rotate v i


-- created on 2025-10-14
