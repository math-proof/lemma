import Lemma.Rat.Eq_0.is.EqInv_0
import Lemma.Hyperreal.InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal
import Lemma.Hyperreal.EqSt_0.of.Infinitesimal
import Lemma.Hyperreal.StDiv.eq.InvStInv
open Hyperreal Rat


@[main, mt]
private lemma left
  {a b : ℝ*}
-- given
  (h_st : stdPart (a / b) ≠ 0)
  (h : a → 0) :
-- imply
  b → 0 := by
-- proof
  apply Infinitesimal.of.Infinitesimal.NotInfinitesimalDiv h
  apply NotInfinitesimal.of.NeSt_0 h_st


@[main, mt]
private lemma main
  {a b : ℝ*}
-- given
  (h_st : stdPart (a / b) ≠ 0)
  (h : b → 0) :
-- imply
  a → 0 := by
-- proof
  rw [StDiv.eq.InvStInv] at h_st
  have h_st := Ne_0.of.NeInv_0 h_st
  apply left h_st h


-- created on 2025-12-16
