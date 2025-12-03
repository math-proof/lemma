import Lemma.Vector.Softmax.eq.Div_SumExp
import Lemma.Vector.SoftmaxSub.eq.Softmax
open Vector


@[main]
private lemma main
  [NeZero n]
  [LT α] [DecidableLT α]
  [ExpPos α]
  [Log α]
-- given
  (x : List.Vector α n) :
-- imply
  log x.softmax = x - x.max - log (exp (x - x.max).sum) := by
-- proof
  have := SoftmaxSub.eq.Softmax x x.max
  have := congrArg log this
  rw [Softmax.eq.Div_SumExp] at this
  rw [← this]
  sorry


-- created on 2025-11-30
-- updated on 2025-12-03
