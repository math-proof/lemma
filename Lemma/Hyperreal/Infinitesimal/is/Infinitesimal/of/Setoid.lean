import Lemma.Hyperreal.EqSt.of.InfinitesimalSub
import Lemma.Hyperreal.EqSt_0.of.Infinitesimal
import Lemma.Hyperreal.InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal
import Lemma.Hyperreal.Setoid.is.OrAndS
open Hyperreal


private lemma mp
  {a b : ℝ*}
-- given
  (h : a ≈ b)
  (h_a : a.Infinitesimal) :
-- imply
  b.Infinitesimal := by
-- proof
  have h_or := OrAndS.of.Setoid h
  simp [h_a] at h_or
  by_contra h_b
  simp [h_b] at h_or
  have := EqSt.of.InfinitesimalSub h_or
  have := InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal h_a h_b
  have := EqSt_0.of.Infinitesimal this
  linarith


@[main, mp, mp.mt]
private lemma main
  {a b : ℝ*}
-- given
  (h : a ≈ b) :
-- imply
  a.Infinitesimal ↔ b.Infinitesimal :=
-- proof
  ⟨mp h, mp h.symm⟩


-- created on 2025-12-27
