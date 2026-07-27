import Lemma.Tensor.LtStackS.of.All_Lt
import Lemma.Tensor.Le.is.LeDataS
open Tensor


@[main]
private lemma main
  [LE α]
  {X Y : Fin n → Tensor α s}
-- given
  (h : ∀ i : Fin n, X i ≤ Y i) :
-- imply
  [i < n] X i ≤ [i < n] Y i := by
-- proof
  unfold Stack
  apply Le.of.LeDataS
  rw [DataFromVector.eq.FlattenMapData, DataFromVector.eq.FlattenMapData]
  simp only [LE.le]
  intro k
  exact LtStackS.of.All_Lt.flatten_map_data (@LE.le α _) (fun i j => by
    have hi := LeDataS.of.Le (h i)
    simp only [LE.le] at hi
    exact hi j) k


-- created on 2026-07-27
