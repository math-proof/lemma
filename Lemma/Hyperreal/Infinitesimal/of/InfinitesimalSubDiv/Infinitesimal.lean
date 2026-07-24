import Lemma.Hyperreal.EqSt.of.InfinitesimalSub
import Lemma.Hyperreal.EqSt_0.of.Infinitesimal
import Lemma.Hyperreal.InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal
import Lemma.Hyperreal.Coe
open Hyperreal


@[main, mt]
private lemma main
  [NeZero (d : ℕ)]
  {a b : ℝ*}
-- given
  (h_a : a → 0)
  (h_b : (a / b - d) → 0) :
-- imply
  b → 0 := by
-- proof
  contrapose! h_b
  rw [Coe d]
  have h_d := NeZero.ne d
  by_contra h
  have h_st := EqSt.of.InfinitesimalSub (x := a / b) (r := (d : ℝ)) (lt_of_not_ge h)
  have h_ab := InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal h_a (not_lt.mpr h_b)
  have h_ab := EqSt_0.of.Infinitesimal h_ab
  simp [h_ab] at h_st
  symm at h_st
  norm_cast at h_st


-- created on 2025-12-09
