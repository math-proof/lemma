import Lemma.Algebra.EqAddSub.of.Ge
open Algebra


@[main]
private lemma main
  {d T l a : ℕ}
-- given
  (h_l : l ≥ a)
  (h_T : T = l - a)
  (h_d : d < T + a) :
-- imply
  d < l := 
-- proof
  EqAddSub.of.Ge h_l ▸ (h_T ▸ h_d)


-- created on 2025-10-06
