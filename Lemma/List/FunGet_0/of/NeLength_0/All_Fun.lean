import Lemma.List.All_Eq_HeadD.of.IsConstant
import Lemma.List.IsConstantTail.of.IsConstant
import Lemma.List.Expr.in.Cons
import Lemma.List.EqCons_Tail.of.NeLength_0
open List


@[main]
private lemma main
  {s : List α}
  {p: α → Prop}
-- given
  (h_ne: s.length ≠ 0)
  (h_all : ∀ t ∈ s, p t) :
-- imply
  p s[0] := by
-- proof
  apply h_all s[0]
  have h_in : s[0] ∈ s[0] :: s.tail := List.Expr.in.Cons
  rwa [EqCons_Tail.of.NeLength_0 h_ne] at h_in


-- created on 2024-07-01
