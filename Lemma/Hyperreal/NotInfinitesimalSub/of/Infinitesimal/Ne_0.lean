import Lemma.Hyperreal.EqSt.of.InfinitesimalSub
import Lemma.Hyperreal.EqSt_0.of.Infinitesimal
open Hyperreal


@[main]
private lemma main
  {x : ℝ*}
  {r : ℝ}
-- given
  (h : Infinitesimal x)
  (h_r : r ≠ 0) :
-- imply
  ¬Infinitesimal (x - r) := by
-- proof
  contrapose! h_r
  have h_r := EqSt.of.InfinitesimalSub h_r
  have h := EqSt_0.of.Infinitesimal h
  rw [h] at h_r
  simp_all


-- created on 2025-12-11
