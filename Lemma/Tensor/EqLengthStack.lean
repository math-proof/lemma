import sympy.tensor.stack
import Lemma.Vector.MapMap.eq.Map_Comp
open Vector


@[main]
private lemma fin
-- given
  (f : Fin n → Tensor α s) :
-- imply
  ([i < n] f i).length = n := by
-- proof
  unfold Stack Tensor.fromVector
  rw [MapMap.eq.Map_Comp]
  unfold Function.comp
  aesop


@[main]
private lemma main
-- given
  (f : ℕ → Tensor α s)
  (n : ℕ) :
-- imply
  ([i < n] f i).length = n := by
-- proof
  apply fin


-- created on 2025-05-23
-- updated on 2025-09-24
