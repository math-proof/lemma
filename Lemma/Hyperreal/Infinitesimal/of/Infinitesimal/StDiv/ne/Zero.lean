import Lemma.Hyperreal.InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal
import Lemma.Hyperreal.EqSt_0.of.Infinitesimal
import Lemma.Hyperreal.StDiv.eq.InvStInv
open Hyperreal


@[main, mt]
private lemma left
  {a b : ℝ*}
-- given
  (h_st : st (a / b) ≠ 0)
  (h : a.Infinitesimal) :
-- imply
  b.Infinitesimal := by
-- proof
  apply Infinitesimal.of.Infinitesimal.NotInfinitesimalDiv h
  apply NotInfinitesimal.of.NeSt_0 h_st


@[main, mt]
private lemma main
  {a b : ℝ*}
-- given
  (h_st : st (a / b) ≠ 0)
  (h : b.Infinitesimal) :
-- imply
  a.Infinitesimal := by
-- proof
  rw [StDiv.eq.InvStInv] at h_st
  simp at h_st
  apply left h_st h


-- created on 2025-12-16
