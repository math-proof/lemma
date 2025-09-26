import Lemma.Tensor.MeanDiv.eq.DivMean
import Lemma.Tensor.Sum.eq.Zero
open Tensor


/--
[Token-Level Policy Gradient Loss](https://arxiv.org/pdf/2503.14476#page=6)

notation is slightly different from pytorch:

X.sum = X.sum (-1)

X.mean = X.mean (-1)
-/
@[main]
private lemma main
  [Semifield float]
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
    repeat rw [Sum.eq.Zero]
    simp [HDiv.hDiv]
    simp [Div.div]
    sorry
  ·
    have hnb : (batch_size : float) ≠ 0 := by
      simp
      sorry
    -- simp [Tensor.mean]
    sorry


-- created on 2025-08-29
-- updated on 2025-09-04
