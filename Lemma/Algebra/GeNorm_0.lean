import Lemma.Basic


@[main]
private lemma main
  [SeminormedAddGroup α]
  {a : α} :
-- imply
  ‖a‖ ≥ 0 :=
-- proof
  norm_nonneg a
