import Lemma.Tensor.MeanDiv.eq.DivMean
import Lemma.Tensor.Sum.eq.Zero
import Lemma.Tensor.EqDiv0_0
import Lemma.Bool.Ne.is.NotEq
import Lemma.Nat.NeCoeS.of.Ne
import Lemma.Tensor.Div.eq.DivDivS.of.Ne_0
import Lemma.Tensor.DataDiv.eq.DivDataS
import Lemma.Vector.GetDiv.eq.DivGetS
import Lemma.Nat.Eq_0
open Tensor Vector Bool Nat
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000


/--
[Token-Level Policy Gradient Loss](https://arxiv.org/pdf/2503.14476#page=6)

notation is slightly different from pytorch:

X.sum = X.sum (-1)

X.mean = X.mean (-1)
-/
@[main]
private lemma main
  [Semifield float]
  [CharZero float]
-- given
  (loss : Tensor float [batch_size, seq_length])
  (mask : Tensor Bool [batch_size, seq_length]) :
-- imply
  let mask : Tensor float [batch_size, seq_length] := mask
  let mask.sum : Tensor float [batch_size] := mask.sum
  let loss.sum : Tensor float [batch_size] := loss.sum
  let mask.sum.mean : Tensor float [] := mask.sum.mean
  loss.sum.sum / mask.sum.sum = (loss.sum / mask.sum.mean).mean := by
-- proof
  intro mask mask.sum loss.sum mask.sum.mean
  rw [MeanDiv.eq.DivMean]
  simp [mask.sum.mean]
  simp [Tensor.mean]
  if hb : batch_size = 0 then
    subst hb
    rw [Sum.eq.Zero (X := loss.sum)]
    rw [Sum.eq.Zero (X := mask.sum)]
    rw [EqDiv0_0.scalar]
    rfl
  else
    rw [Div.eq.DivDivS.of.Ne_0 (A := ↑batch_size)]
    .
      simp [HDiv.hDiv]
      apply Eq.of.EqDataS
      ext i
      simp [Div.eq.HDiv]
      simp [DataDiv.eq.DivDataS]
      simp [GetDiv.eq.DivGetS.fin]
      simp [Eq_0.prod]
      simp [GetElem.getElem]
    .
      have := Ne.of.NotEq hb
      simp_all


-- created on 2025-08-29
-- updated on 2025-09-04
