import Lemma.Hyperreal.Infinite.is.InfiniteAdd.of.NotInfinite
import Lemma.Hyperreal.NotInfinite
import Lemma.Nat.Add
open Hyperreal Nat


private lemma mp
  {x : ℝ*}
-- given
  (h : Infinite x)
  (r : ℝ) :
-- imply
  Infinite (x + r) := by
-- proof
  rw [Add.comm]
  apply InfiniteAdd.of.Infinite.NotInfinite _ h
  apply NotInfinite


/--
| attributes | lemma |
| :---: | :---: |
| main | Hyperreal.Infinite.is.InfiniteAdd |
| comm | Hyperreal.InfiniteAdd.is.Infinite |
| mp   | Hyperreal.InfiniteAdd.of.Infinite |
| mpr  | Hyperreal.Infinite.of.InfiniteAdd |
| mp.mt | Hyperreal.NotInfinite.of.NotInfiniteAdd |
| mpr.mt | Hyperreal.NotInfiniteAdd.of.NotInfinite |
-/
@[main, comm, mp, mpr, mp.mt, mpr.mt]
private lemma main
-- given
  (x : ℝ*)
  (r : ℝ) :
-- imply
  Infinite x ↔ Infinite (x + r) := by
-- proof
  constructor <;>
    intro h
  ·
    apply mp h
  ·
    have h := mp h (-r)
    simp at h
    exact h


@[main, comm, mp, mpr, mp.mt, mpr.mt]
private lemma left
-- given
  (r : ℝ)
  (x : ℝ*) :
-- imply
  Infinite x ↔ Infinite (r + x) := by
-- proof
  rw [Add.comm]
  apply main


-- created on 2025-12-11
-- updated on 2025-12-19
