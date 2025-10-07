import Lemma.Bool.AndAllSSetOf.of.All
open Bool


@[main]
private lemma main
  {p : α → Prop}
  {S : Set α}
-- given
  (h : ∀ e, p e) :
-- imply
  ∀ e ∈ S, p e := by
-- proof
  have := AndAllSSetOf.of.All h fun e => e ∈ S
  exact this.left


-- created on 2025-04-29
