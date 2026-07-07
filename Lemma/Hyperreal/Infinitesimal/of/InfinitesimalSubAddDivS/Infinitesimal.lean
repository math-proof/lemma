import Lemma.Hyperreal.EqSt.of.InfinitesimalSub
import Lemma.Hyperreal.EqSt_0.of.Infinitesimal
import Lemma.Hyperreal.InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal
import Lemma.Hyperreal.InfinitesimalSub.of.Infinitesimal.Infinitesimal
import Lemma.Hyperreal.StDiv.eq.InvStInv
import Lemma.Hyperreal.EqCoeS
open Hyperreal


@[main, mt]
private lemma main
  [NeZero (d : ℕ)]
  {a b : ℝ*}
-- given
  (h_a : a → 0)
  (h_b : (a / b + b / a - d) → 0) :
-- imply
  b → 0 := by
-- proof
  contrapose! h_b
  rw [EqCoeS d]
  by_contra h
  have h_ab := InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal h_a (not_lt.mpr h_b)
  rw [show a / b + b / a - (d : ℝ) = (a / b) + (b / a - (d : ℝ)) by ring] at h
  have h_ba := InfinitesimalSub.of.Infinitesimal.Infinitesimal (lt_of_not_ge h) h_ab
  simp at h_ba
  have h_ba := EqSt.of.InfinitesimalSub (show (b / a - (d : ℝ)) → 0 from h_ba)
  have h_ab := EqSt_0.of.Infinitesimal h_ab
  rw [StDiv.eq.InvStInv] at h_ab
  simp_all


-- created on 2025-12-10
