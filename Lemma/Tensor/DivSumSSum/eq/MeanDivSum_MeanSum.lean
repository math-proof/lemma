import Lemma.Tensor.MeanDiv.eq.DivMean
import Lemma.Tensor.Sum.eq.Zero
import Lemma.Tensor.EqDiv0'0
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
  [Field float]
  [CharZero float]
-- given
  (loss : Tensor float [batch_size, seq_length])
  (mask : Tensor Bool [batch_size, seq_length]) :
-- imply
  let mask : Tensor float [batch_size, seq_length] := mask
  let mask_sum : Tensor float [batch_size] := mask.sum
  let loss_sum : Tensor float [batch_size] := loss.sum
  let mask_sum_mean : Tensor float [] := mask_sum.mean
  loss_sum.sum / mask_sum.sum = (loss_sum / mask_sum_mean).mean := by
-- proof
  intro mask mask_sum loss_sum mask_sum_mean
  rw [MeanDiv.eq.DivMean]
  simp [mask_sum_mean]
  simp [Tensor.mean]
  by_cases hb : batch_size = 0
  ·
    subst hb
    rw [Sum.eq.Zero (X := loss_sum)]
    rw [Sum.eq.Zero (X := mask_sum)]
    rw [EqDiv0'0.scalar]
    rfl
  ·
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
      have hb := Ne.of.NotEq hb
      simpa [NeCoeS.of.Ne hb (Z := float)]


-- created on 2025-08-29
-- updated on 2025-09-04
