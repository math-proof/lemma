import Lemma.Nat.EqMulDiv.of.Dvd
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.MapCast.as.Map.of.Eq
import Lemma.Vector.RepeatMap.eq.MapRepeat
open Nat Tensor Vector


@[main]
private lemma main
  [Semifield α]
  {s' : List ℕ}
-- given
  (h : s.prod ∣ s'.prod)
  (X : Tensor α s)
  (B : Tensor α []) :
-- imply
  (X / B).reshape s' h = X.reshape s' h / B := by
-- proof
  apply Eq.of.EqDataS
  unfold Tensor.reshape
  dsimp only [HDiv.hDiv]
  have h_len := EqMulDiv.of.Dvd h
  rw [MapCast.eq.Cast_Map.of.Eq h_len]
  apply congrArg (cast (congrArg (List.Vector α) h_len))
  apply RepeatMap.eq.MapRepeat X.data (· / B.data[0])


-- created on 2026-08-12
