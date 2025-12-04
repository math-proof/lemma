import Lemma.Real.NeExp_0
import Lemma.Vector.GetExp.eq.ExpGet
import Lemma.Vector.EqLogExp
import Lemma.Vector.LogDiv.eq.SubLogS.of.All_Ne_0.Ne_0
import Lemma.Vector.NeSumExp_0
import Lemma.Vector.Softmax.eq.Div_SumExp
import Lemma.Vector.SoftmaxSub.eq.Softmax
open Vector Real


@[main]
private lemma main
  [NeZero n]
  [LT α] [DecidableLT α]
  [LogPos α]
  [IsOrderedCancelAddMonoid α]
-- given
  (x : List.Vector α n) :
-- imply
  log x.softmax = x - x.max - log (exp (x - x.max)).sum := by
-- proof
  have := SoftmaxSub.eq.Softmax x x.max
  have := congrArg Log.log this
  rw [Softmax.eq.Div_SumExp] at this
  rw [← this]
  rw [LogDiv.eq.SubLogS.of.All_Ne_0.Ne_0]
  ·
    rw [@Vector.EqLogExp]
  ·
    intro i
    rw [GetExp.eq.ExpGet]
    apply NeExp_0
  ·
    apply NeSumExp_0


-- created on 2025-11-30
-- updated on 2025-12-04
