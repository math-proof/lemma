import Lemma.Tensor.EqGet0_0
import Lemma.Tensor.GtLength
import Lemma.Tensor.LeGetS.of.Le
import Lemma.Tensor.Length
import sympy.tensor.tensor
open Tensor


@[main, fin]
private lemma main
  [LE α]
  [Zero α]
  {A : Tensor α s}
-- given
  (h : A ≥ 0)
  (i : Fin A.length) :
-- imply
  A[i] ≥ 0 := by
  let i₀ : Fin (0 : Tensor α s).length := Fin.cast (Length (0 : Tensor α s) A).symm i
  have h' := LeGetS.of.Le h i₀
  have hle : 0 ≤ A[i₀]'(GtLength i₀ A) := by
    rw [← EqGet0_0 i₀]
    grind
  simpa [i₀, Fin.cast] using hle


-- created on 2026-07-28
