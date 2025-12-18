import Lemma.Hyperreal.InfiniteDiv.of.Infinite.NotInfinite
import Lemma.Hyperreal.EqSt_0.of.Infinitesimal
import Lemma.Hyperreal.EqSt0'0
import Lemma.Hyperreal.EqSt_0.of.Infinite
import Lemma.Hyperreal.StDiv.eq.InvStInv
open Hyperreal


@[main, mt]
private lemma left
  {a b : ℝ*}
-- given
  (h_st : st (a / b) ≠ 0)
  (h : a.Infinite) :
-- imply
  b.Infinite := by
-- proof
  if h_b : b = 0 then
    subst h_b
    simp [EqSt0'0] at h_st
  else
    have : NeZero b := ⟨h_b⟩
    apply Infinite.of.Infinite.NotInfiniteDiv h
    apply NotInfinite.of.NeSt_0 h_st


@[main, mt]
private lemma main
  {a b : ℝ*}
-- given
  (h_st : st (a / b) ≠ 0)
  (h : b.Infinite) :
-- imply
  a.Infinite := by
-- proof
  rw [StDiv.eq.InvStInv] at h_st
  simp at h_st
  apply left h_st h


-- created on 2025-12-17
