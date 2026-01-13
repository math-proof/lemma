import Lemma.Nat.GtMul.of.Gt_0.Gt_1
import Lemma.Nat.Mul
import Lemma.Tensor.SEqRepeat.of.Eq0Get
import Lemma.Tensor.SEqRepeat_1
open Tensor Nat


@[main]
private lemma main
  {s : List ℕ}
  {d : Fin s.length}
-- given
  (h : n * s[d] = s[d])
  (X : Tensor α s) :
-- imply
  X.repeat n d ≃ X := by
-- proof
  if h_n : n = 1 then
    subst h_n
    apply SEqRepeat_1
  else
    apply SEqRepeat.of.Eq0Get
    if h_n : n = 0 then
      subst h_n
      simp_all
    else
      have h_n : n > 1 := by omega
      by_contra h_d
      rw [Mul.comm] at h
      have := GtMul.of.Gt_0.Gt_1 (by omega) h_n (a := s[d])
      omega


-- created on 2026-01-13
