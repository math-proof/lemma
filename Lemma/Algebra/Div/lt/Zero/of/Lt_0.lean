import Lemma.Algebra.Div.lt.Zero.of.Gt_0.Lt_0
import Lemma.Algebra.GtCoe_0.is.Gt_0
open Algebra


@[main]
private lemma main
  [NeZero (d : ℕ)]
  [LinearOrderedField α]
  {x : α}
-- given
  (h : x < 0) :
-- imply
  d / x < 0 := by
-- proof
  have d_pos : (d : α) > 0 := by 
    apply GtCoe_0.of.Gt_0
    exact NeZero.pos d
  apply Div.lt.Zero.of.Gt_0.Lt_0 d_pos h


-- created on 2025-07-20
-- updated on 2025-08-02
