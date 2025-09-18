import Lemma.Basic


@[main, comm, mp, mpr]
private lemma main
  [InvolutiveNeg α]
-- given
  (x y : α) :
-- imply
  -x = -y ↔ x = y :=
-- proof
  neg_inj


-- created on 2025-03-16
