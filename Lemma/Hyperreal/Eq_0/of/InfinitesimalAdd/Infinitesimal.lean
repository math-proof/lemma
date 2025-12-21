import Lemma.Hyperreal.NotInfinitesimalSub.of.Infinitesimal.Ne_0
import Lemma.Nat.Add
open Hyperreal Nat


/--
| attributes | lemma |
| :---: | :---: |
| main | Hyperreal.Eq_0.of.InfinitesimalAdd.Infinitesimal |
| mt   | Hyperreal.NotInfinitesimalAdd.of.Ne_0.Infinitesimal |
-/
@[main, mt]
private lemma main
  {x : ℝ*}
  {r : ℝ}
-- given
  (h : Infinitesimal x)
  (h_r : Infinitesimal (x + r)) :
-- imply
  r = 0 := by
-- proof
  contrapose! h_r
  have := NotInfinitesimalSub.of.Infinitesimal.Ne_0 h (by simpa) (r := -r)
  simp at this
  assumption


@[main, mt]
private lemma left
  {x : ℝ*}
  {r : ℝ}
-- given
  (h : Infinitesimal x)
  (h_r : Infinitesimal (r + x)) :
-- imply
  r = 0 := by
-- proof
  rw [Add.comm] at h_r
  apply main h h_r


-- created on 2025-12-11
-- updated on 2025-12-21
