import Lemma.Hyperreal.EqSt.of.InfinitesimalSub
import Lemma.Hyperreal.EqSt_0.of.Infinitesimal
import Lemma.Hyperreal.InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal
open Hyperreal


@[main]
private lemma main
  [NeZero (d : ℕ)]
  {a b : ℝ*}
-- given
  (h_a : Infinitesimal a)
  (h_b : ¬Infinitesimal b) :
-- imply
  ¬Infinitesimal (a / b - d) := by
-- proof
  suffices ¬Infinitesimal (a / b - (d : ℝ)) by
    exact this
  have h_d := NeZero.ne d
  by_contra h
  have h := EqSt.of.InfinitesimalSub h
  have h_ab := InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal h_a h_b
  have h_ab := EqSt_0.of.Infinitesimal h_ab
  simp [h_ab] at h
  symm at h
  norm_cast at h


-- created on 2025-12-09
