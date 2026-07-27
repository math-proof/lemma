import Lemma.Tensor.EqStack_0'0
import Lemma.Tensor.LeStackS.of.All_Le
import sympy.tensor.stack
open Tensor


@[main]
private lemma main
  [LE α]
  [Zero α]
  {X : Fin n → Tensor α s}
-- given
  (h : ∀ i : Fin n, X i ≥ 0) :
-- imply
  [i < n] X i ≥ 0 := by
-- proof
  apply ge_iff_le.mpr
  rw [← EqStack_0'0]
  exact LeStackS.of.All_Le (X := fun _ => (0 : Tensor α s)) (Y := X) (fun i => ge_iff_le.mp (h i))


-- created on 2026-07-26
-- updated on 2026-07-27
