import Lemma.Hyperreal.EqSt.of.InfinitesimalSub
import Lemma.Hyperreal.EqSt_0.of.Infinitesimal
import Lemma.Hyperreal.InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal
open Hyperreal


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : Infinitesimal a)
  (h_b : ¬Infinitesimal b) :
-- imply
  ¬Infinitesimal (a / b - 1) := by
-- proof
  by_contra h
  have h := EqSt.of.InfinitesimalSub h
  have h_ab := InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal h_a h_b
  have h_ab := EqSt_0.of.Infinitesimal h_ab
  simp [h_ab] at h


-- created on 2025-12-09
