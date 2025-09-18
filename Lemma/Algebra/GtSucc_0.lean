import Lemma.Basic


@[main]
private lemma main
  {a : ℕ} :
-- imply
  a.succ > 0 :=
-- proof
  Nat.succ_pos a


-- created on 2025-05-04
