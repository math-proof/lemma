import Lemma.Tensor.Log.Softmax.eq.Add.LogSumExp
open Tensor


@[main]
private lemma main
  [NeZero n]
  {x : Fin n → ℝ} :
-- imply
  (fun i => x i - Real.log (∑ j, Real.exp (x j))) = fun i => Real.log (Real.exp (x i) / ∑ j, Real.exp (x j)) :=
-- proof
  Log.Softmax.eq.Add.LogSumExp.symm


-- created on 2022-03-31
