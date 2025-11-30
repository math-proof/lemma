import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqData0'0
import Lemma.Vector.Eq.is.All_EqGetS
import Lemma.Vector.Sum.eq.Zero
open Tensor Vector


@[main]
private lemma main
  [Add α] [Zero α]
-- given
  (X : Tensor α (0 :: s)) :
-- imply
  X.sum 0 = 0 := by
-- proof
  simp [Tensor.sum]
  apply Eq.of.EqDataS
  simp [EqData0'0]
  apply Eq.of.All_EqGetS
  simp [Sum.eq.Zero]


-- created on 2025-09-04
-- updated on 2025-11-30
