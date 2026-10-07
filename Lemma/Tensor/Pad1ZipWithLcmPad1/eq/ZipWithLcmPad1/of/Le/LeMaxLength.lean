import sympy.core.mul
import sympy.Basic
import Lemma.Tensor.Pad1.eq.AppendReplicateSub1Pad1.of.Le.Le_Length
import Lemma.List.LengthZipWithLcm.eq.Length.of.EqLengthS
import Lemma.List.ZipWithLcmReplicate1.eq.Replicate1
open Tensor List


@[main]
private lemma main
  {n m : ℕ}
-- given
  (s s' : List ℕ)
  (hn : s.length ⊔ s'.length ≤ n)
  (hm : n ≤ m) :
-- imply
  pad1 ((pad1 s n).zipWith Nat.lcm (pad1 s' n)) m =
      (pad1 s m).zipWith Nat.lcm (pad1 s' m) := by
-- proof
  have hs : s.length ≤ n := le_trans le_sup_left hn
  have hs' : s'.length ≤ n := le_trans le_sup_right hn
  have hlen : (pad1 s n).length = (pad1 s' n).length := by
    rw [pad1_length s n hs, pad1_length s' n hs']
  rw [Pad1.eq.AppendReplicateSub1Pad1.of.Le.Le_Length s hs hm, Pad1.eq.AppendReplicateSub1Pad1.of.Le.Le_Length s' hs' hm,
    List.zipWith_append (by simp), ZipWithLcmReplicate1.eq.Replicate1]
  have hzip_len : ((pad1 s n).zipWith Nat.lcm (pad1 s' n)).length = n := by
    rw [LengthZipWithLcm.eq.Length.of.EqLengthS _ _ hlen, pad1_length s n hs]
  change
    List.replicate (m - ((pad1 s n).zipWith Nat.lcm (pad1 s' n)).length) 1 ++
        (pad1 s n).zipWith Nat.lcm (pad1 s' n) =
      List.replicate (m - n) 1 ++ (pad1 s n).zipWith Nat.lcm (pad1 s' n)
  rw [hzip_len]


-- created on 2026-10-07
