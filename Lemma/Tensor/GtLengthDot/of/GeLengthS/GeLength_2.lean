import Lemma.List.EqAppendDropLast.of.GtLength_0
import Lemma.List.EqAppendTake__ListGet.of.GeLength_2
import Lemma.List.EqCons_Tail.of.GtLength_0
import Lemma.Tensor.GtLengthDot.of.GeLengthS
open List Tensor


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h : s'.length ≥ 2)
  (h_s : s.length ≥ s'.length)
  (X : Tensor α s)
  (Y : Tensor α s')
  (i : Fin s[0]) :
-- imply
  i < (X @ Y).length := by
-- proof
  let s_batch := s.tail.dropLast
  let batch_size' := s'.take (s'.length - 2)
  have h_tail : s.tail.length > 0 := by grind
  have h_X : s = s[0] :: (s_batch ++ [s[s.length - 1]]) := calc
    _ = s[0] :: s.tail := (EqCons_Tail.of.GtLength_0 (by omega)).symm
    _ = s[0] :: (s_batch ++ [s[s.length - 1]]) := by
      congr 1
      dsimp only [s_batch]
      have h_get : s.tail[s.tail.length - 1] = s[s.length - 1] := by grind
      calc
        _ = s.tail.dropLast ++ [s.tail[s.tail.length - 1]] := (EqAppendDropLast.of.GtLength_0 h_tail).symm
        _ = s.tail.dropLast ++ [s[s.length - 1]] := by rw [h_get]
  have h_Y : s' = batch_size' ++ [s'[s'.length - 2], s'[s'.length - 1]] := (EqAppendTake__ListGet.of.GeLength_2 h).symm
  have h_batch : s_batch.length ≥ batch_size'.length := by
    dsimp only [s_batch, batch_size']
    simp only [length_dropLast, length_tail, length_take]
    omega
  let X' := cast (congrArg (Tensor α) h_X) X
  let Y' := cast (congrArg (Tensor α) h_Y) Y
  have h_dot := GtLengthDot.of.GeLengthS h_batch X' Y' i
  have h_len : (X @ Y).length = (X' @ Y').length := by
    dsimp [Tensor.length]
    grind
  exact h_len ▸ h_dot


-- created on 2026-07-20
