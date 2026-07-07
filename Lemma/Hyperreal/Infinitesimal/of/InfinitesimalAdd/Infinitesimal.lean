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
  (h : (x + y) → 0)
  (h_x : x → 0) :
-- imply
  y → 0 := by
-- proof
  have h_sub := InfinitesimalSub.of.Infinitesimal.Infinitesimal h h_x
  simp at h_sub
  assumption


-- created on 2025-12-20
