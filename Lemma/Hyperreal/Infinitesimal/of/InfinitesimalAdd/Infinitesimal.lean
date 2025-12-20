import Lemma.Hyperreal.InfinitesimalSub.of.Infinitesimal.Infinitesimal
open Hyperreal


/--
the hypotheses are arranged in the constructor order of substraction x + y - y

| attributes | lemma |
| :---: | :---: |
| main | Hyperreal.Infinitesimal.of.InfinitesimalAdd.Infinitesimal |
| mt 1 | Hyperreal.NotInfinitesimalAdd.of.NotInfinitesimal.Infinitesimal |
-/
@[main, mt 1]
private lemma main
  {x y : ℝ*}
-- given
  (h : Infinitesimal (x + y))
  (h_x : Infinitesimal x) :
-- imply
  Infinitesimal y := by
-- proof
  have h_sub := InfinitesimalSub.of.Infinitesimal.Infinitesimal h h_x
  simp at h_sub
  assumption


-- created on 2025-12-20
