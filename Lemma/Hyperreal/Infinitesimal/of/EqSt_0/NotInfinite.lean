import Lemma.Hyperreal.EqSt_0.is.Infinite.ou.Infinitesimal
open Hyperreal


/--
| attributes | lemma |
| :---: | :---: |
| main | Hyperreal.Infinitesimal.of.EqSt_0.NotInfinite |
| mt | Hyperreal.NeSt_0.of.NotInfinitesimal.NotInfinite |
| mt 1 | Hyperreal.Infinite.of.EqSt_0.NotInfinitesimal |
-/
@[main, mt, mt 1]
private lemma main
  {x : ℝ*}
-- given
  (h_infty : ¬x → ∞)
  (h : stdPart x = 0) :
-- imply
  x → 0 := by
-- proof
  rw [EqSt_0.is.Infinite.ou.Infinitesimal] at h
  simp [h_infty] at h
  assumption


-- created on 2026-07-26
