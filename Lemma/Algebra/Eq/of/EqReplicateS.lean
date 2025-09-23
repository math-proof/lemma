import Lemma.Algebra.EqGetS.of.Eq.Lt
import Lemma.Vector.EqGetReplicate.of.Lt
open Algebra Vector


@[main]
private lemma main
-- given
  (h_n : n > 0)
  (h : List.Vector.replicate n a = List.Vector.replicate n b) :
-- imply
  a = b := by
-- proof
  have := EqGetS.of.Eq.Lt h_n h
  simp at this
  repeat rw [EqGetReplicate.of.Lt] at this
  assumption


-- created on 2025-07-06
