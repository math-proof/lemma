import Lemma.Basic


@[main]
private lemma main
-- given
  (n d : ℕ) :
-- imply
  n % d % d = n % d :=
-- proof
  Nat.mod_mod n d


-- created on 2025-06-16
