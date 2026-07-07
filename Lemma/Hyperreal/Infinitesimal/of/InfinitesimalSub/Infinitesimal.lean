import Lemma.Hyperreal.InfinitesimalSub
import Lemma.Hyperreal.Infinitesimal.of.Infinitesimal.InfinitesimalSub
open Hyperreal


/--
constructor order of addition of (a - b) + b = a

| attributes | lemma |
| :---: | :---: |
| main | Hyperreal.Infinitesimal.of.InfinitesimalSub.Infinitesimal |
| mt 1 | Hyperreal.NotInfinitesimalSub.of.NotInfinitesimal.Infinitesimal |
-/
@[main, mt 1]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : (a - b) → 0)
  (h_b : b → 0) :
-- imply
  a → 0 := by
-- proof
  have := InfinitesimalAdd.of.Infinitesimal.Infinitesimal h_a h_b
  simp_all


-- created on 2025-12-10
-- updated on 2025-12-20
