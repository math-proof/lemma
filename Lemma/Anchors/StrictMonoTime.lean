import Lemma.Anchors.Time.lt.TimeAdd1
open Finset Filter


@[main]
private lemma main
  {α : ℕ → ℝ}
  {anc : Anchors α} :
-- imply
  StrictMono anc.t :=
-- proof
  strictMono_nat_of_lt_succ fun _ => Anchors.Time.lt.TimeAdd1


-- created on 2026-09-26