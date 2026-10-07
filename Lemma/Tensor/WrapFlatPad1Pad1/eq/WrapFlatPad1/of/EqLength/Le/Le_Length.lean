import sympy.core.mul
import sympy.Basic
import Lemma.Tensor.Pad1.eq.AppendReplicateSub1Pad1.of.Le.Le_Length
import Lemma.Tensor.WrapFlatAppendReplicate1.eq.WrapFlat
open Tensor


@[main]
private lemma main
  {n m : ℕ}
-- given
  (s out : List ℕ)
  (hn : s.length ≤ n)
  (hm : n ≤ m)
  (hout : out.length = n)
  (i : ℕ) :
-- imply
  wrapFlat (pad1 s m) (pad1 out m) i = wrapFlat (pad1 s n) out i := by
-- proof
  rw [Pad1.eq.AppendReplicateSub1Pad1.of.Le.Le_Length s hn hm]
  have : pad1 out m = List.replicate (m - n) 1 ++ out := by
    simp [pad1, hout]
  rw [this, WrapFlatAppendReplicate1.eq.WrapFlat]


-- created on 2026-10-07
