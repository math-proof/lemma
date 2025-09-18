import Lemma.Set.In.of.In_SDiff
open Set


@[main]
private lemma main
  {f : α → Prop}
  {S : Set α}
-- given
  (h : ∀ e ∈ S, f e)
  (X : Set α):
-- imply
  ∀ e ∈ S \ X, f e := by
-- proof
  intro e h_e
  apply h
  apply In.of.In_SDiff h_e


-- created on 2025-07-19
