import Lemma.Hyperreal.Infinite.of.InfinitesimalDiv.NotInfinitesimal
import Lemma.Hyperreal.NotInfinite.of.Infinitesimal
open Hyperreal


/--
the hypotheses are arranged in the constructor order of multiplication a / b * b

| attributes | lemma |
| :---: | :---: |
| main | Hyperreal.Infinitesimal.of.InfinitesimalDiv.Infinitesimal |
| mt   | Hyperreal.NotInfinitesimal.of.InfinitesimalDiv.NotInfinitesimal |
| mt 1 | Hyperreal.NotInfinitesimalDiv.of.NotInfinitesimal.Infinitesimal |
-/
@[main, mt, mt 1]
private lemma main
  [NeZero (b : ℝ*)]
  {a : ℝ*}
-- given
  (h : Infinitesimal (a / b))
  (h_a : Infinitesimal b) :
-- imply
  Infinitesimal a := by
-- proof
  contrapose! h_a
  have := Infinite.of.InfinitesimalDiv.NotInfinitesimal h_a h
  apply NotInfinitesimal.of.Infinite this


-- created on 2025-12-20
