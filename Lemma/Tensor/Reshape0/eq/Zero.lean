import Def.Data.Tensor.Reshape
import Lemma.Tensor.EqData0'0
import Lemma.Tensor.Eq.is.EqDataS
import Theorem.Vector.Zero.eq.Replicate
import Lemma.Vector.EqCast_0'0.of.Eq
open Tensor Vector


@[path]
private lemma main
  [Zero α]
  {s s' : List ℕ}
-- given
  (h : s.prod ∣ s'.prod) :
-- imply
  (0 : Tensor α s).reshape s' h = 0 := by
-- proof
  apply Eq.of.EqDataS
  have h_repeat : (0 : List.Vector α s.prod).repeat (s'.prod / s.prod) = 0 := by
    simp only [Zero.eq.Replicate]
    apply Subtype.ext
    change ((List.replicate (s'.prod / s.prod) (List.Vector.replicate s.prod (0 : α))).map
      List.Vector.toList).flatten = List.replicate _ 0
    rw [List.map_replicate]
    apply List.flatten_replicate_replicate
  simp only [Tensor.reshape, EqData0'0, h_repeat]
  rw [EqCast_0'0.of.Eq (Nat.EqMulDiv.of.Dvd h)]


-- created on 2026-09-16
-- updated on 2026-11-20
