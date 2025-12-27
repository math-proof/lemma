import Lemma.Hyperreal.InfinitesimalAdd.of.Infinitesimal.Infinitesimal
import Lemma.Hyperreal.InfinitesimalSub
open Hyperreal


/--
constructor order of substraction of a - (a - b) = b

| attributes | lemma |
| :---: | :---: |
| main | Hyperreal.Infinitesimal.of.Infinitesimal.InfinitesimalSub |
| mt | Hyperreal.NotInfinitesimalSub.of.Infinitesimal.NotInfinitesimal |
-/
@[main, mt]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : Infinitesimal a)
  (h_b : Infinitesimal (a - b)) :
-- imply
  Infinitesimal b := by
-- proof
  have h_b := InfinitesimalSub.comm.mp h_b
  have := InfinitesimalAdd.of.Infinitesimal.Infinitesimal h_a h_b
  simp_all


-- created on 2025-12-10
-- updated on 2025-12-20
