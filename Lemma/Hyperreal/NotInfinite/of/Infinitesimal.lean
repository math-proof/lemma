import Lemma.Hyperreal.Infinitesimal.is.All_LtAbs
import Lemma.Hyperreal.NotInfinite.is.Any_LeAbs
open Hyperreal


@[main, mt]
private lemma main
  {x : ℝ*}
-- given
  (h : x.Infinitesimal) :
-- imply
  ¬x.Infinite := by
-- proof
  rw [NotInfinite.is.Any_LeAbs]
  use 1
  simp
  have h := All_LtAbs.of.Infinitesimal h
  have h := h 1
  simp at h
  linarith


-- created on 2025-12-16
