import Lemma.List.Ne_Nil.is.GeLength_1
import Lemma.Tensor.Einsum.eq.Bmm
import Lemma.Tensor.GetDot.eq.DotGet.of.Eq
import Lemma.Tensor.GetDot.eq.DotGet.of.Gt
import Lemma.Tensor.GetDot.eq.DotGet.of.Lt
import Lemma.Tensor.GtLengthDot.of.LeLengthS.Ne_Nil
open List Tensor
set_option maxHeartbeats 10000000


@[main, fin]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (X : Tensor α [n, k])
  (Y : Tensor α [n', k'])
  (i : Fin n) :
-- imply
  (X @ Y)[i]'(GtLengthDot.of.LeLengthS.Ne_Nil (by simp) (by apply GeLength_1.of.Ne_Nil (by simp)) X Y i) = X[i] @ Y := by
-- proof
  if h_n : k < n' then
    apply GetDot.eq.DotGet.of.Lt h_n
  else if h_n : k > n' then
    apply GetDot.eq.DotGet.of.Gt (by omega)
  else
    have h_n : k = n' := by omega
    subst h_n
    have := GetDot.eq.DotGet.of.Eq.akin X Y i
    simp [Dot.dot] at this ⊢
    simpa [Einsum.eq.Bmm]


@[main, fin]
private lemma une
  [Mul α] [Add α] [Zero α]
-- given
  (X : Tensor α [n, k])
  (Y : Tensor α [n'])
  (i : Fin n) :
-- imply
  (X @ Y)[i]'(GtLengthDot.of.LeLengthS.Ne_Nil (by simp) (by apply GeLength_1.of.Ne_Nil (by simp)) X Y i) = X[i] @ Y := by
-- proof
  if h_n : k < n' then
    apply GetDot.eq.DotGet.of.Lt.une h_n
  else if h_n : k > n' then
    apply GetDot.eq.DotGet.of.Gt.une (by omega)
  else
    have h_n : k = n' := by omega
    subst h_n
    have := GetDot.eq.DotGet.of.Eq.akin.une X Y i
    simp [Dot.dot] at this ⊢
    simpa [Einsum.eq.Bmm]


-- created on 2026-01-05
-- updated on 2026-07-15
