import Lemma.Nat.EqMulDiv.of.Dvd
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.MapCast.as.Map.of.Eq
import Lemma.Vector.RepeatMap.eq.MapRepeat
open Nat Tensor Vector


@[main, comm]
private lemma main
  {s' : List ℕ}
  {f : α → β}
-- given
  (h : s.prod ∣ s'.prod)
  (X : Tensor α s) :
-- imply
  (X.map f).reshape s' h = (X.reshape s' h).map f := by
-- proof
  apply Eq.of.EqDataS
  unfold Tensor.reshape Tensor.map
  have h_len := EqMulDiv.of.Dvd h
  rw [MapCast.eq.Cast_Map.of.Eq h_len]
  apply congrArg (cast (congrArg (List.Vector β) h_len))
  apply RepeatMap.eq.MapRepeat X.data f


-- created on 2026-08-16
