import Lemma.Nat.EqMulDiv.of.Dvd
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.MapCast.as.Map.of.Eq
import Lemma.Vector.RepeatMap.eq.MapRepeat
open Nat Tensor Vector


@[main]
private lemma main
  {s' : List ℕ}
-- given
  (f : α → α → α)
  (h : s.prod ∣ s'.prod)
  (X : Tensor α s)
  (B : Tensor α []) :
-- imply
  (X.map (f · B.data[0])).reshape s' h = (X.reshape s' h).map (f · B.data[0]) := by
-- proof
  apply Eq.of.EqDataS
  unfold Tensor.reshape Tensor.map
  have h_len := EqMulDiv.of.Dvd h
  rw [MapCast.eq.Cast_Map.of.Eq h_len]
  apply congrArg (cast (congrArg (List.Vector α) h_len))
  apply RepeatMap.eq.MapRepeat X.data (f · B.data[0])


-- created on 2026-08-15
