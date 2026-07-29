import Lemma.Tensor.EqGet0_0
import Lemma.Tensor.GtLength
import Lemma.Tensor.LtGetS.of.Lt
import Lemma.Tensor.Length
import sympy.tensor.tensor
open Tensor


@[main, fin]
private lemma main
  [LT α]
  [Zero α]
  {A : Tensor α s}
-- given
  (h : A > 0)
  (i : Fin A.length) :
-- imply
  A[i] > 0 := by
  let i₀ : Fin (0 : Tensor α s).length := Fin.cast (Length (0 : Tensor α s) A).symm i
  have h' := LtGetS.of.Lt h i₀
  have hgt : 0 < A[i₀]'(GtLength i₀ A) := by
    rw [← EqGet0_0 i₀]
    grind
  simpa [i₀, Fin.cast] using hgt


-- created on 2026-07-29
