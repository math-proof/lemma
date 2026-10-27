import Initialize.Tactic.Attr.Basic


@[path, comm]
private lemma main
  [Mul M] [One M]
-- given
  (a : M)
  (l : List M) :
-- imply
  (a :: l).prod = a * l.prod :=
-- proof
  List.prod_cons


-- created on 2024-07-01
-- updated on 2026-10-26
