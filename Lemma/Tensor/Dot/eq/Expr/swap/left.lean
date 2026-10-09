import sympy.matrices.expressions.permutation
import sympy.vector.Basic
import Lemma.Tensor.DotDot.eq.Dot_Dot
import Lemma.Tensor.DotGetSwapMatrix.eq.Get
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.GetDot.eq.DotGet
open Tensor


@[path]
private lemma main
  [Semiring α] [CharZero α]
-- given
  (x : Tensor α [n])
  (i j : Fin n) :
-- imply
  let P : Tensor α [n, n] := SwapMatrix n i j
  (P @ P) @ x = x := by
-- proof
  intro P
  simp only [P]
  rw [DotDot.eq.Dot_Dot.mmv (SwapMatrix (α := α) n i j) (SwapMatrix (α := α) n i j) x]
  apply Eq.of.All_EqGetS.fin
  intro k
  apply Eq.trans (GetDot.eq.DotGet.une (SwapMatrix (α := α) n i j) ((SwapMatrix (α := α) n i j) @ x) k)
  apply Eq.trans (DotGetSwapMatrix.eq.Get ((SwapMatrix (α := α) n i j) @ x) i j k)
  apply Eq.trans (GetDot.eq.DotGet.une (SwapMatrix (α := α) n i j) x (Equiv.swap i j k))
  apply Eq.trans (DotGetSwapMatrix.eq.Get x i j (Equiv.swap i j k))
  rw [Equiv.swap_apply_self]
  rfl


-- created on 2020-11-14
