import sympy.vector.vector
import Lemma.Vector.Eq.of.Val
open Vector


/--
| attributes | lemma |
| :---: | :---: |
| main | Vector.Eq.is.ToList |
| comm | Vector.ToList.is.Eq |
| mp | Vector.ToList.of.Eq |
| mpr | Vector.Eq.of.ToList |
-/
@[main, comm, mp, mpr]
private lemma main
  {a b : List.Vector α n} :
-- imply
  a = b ↔ a.toList = b.toList := by
-- proof
  constructor
  ·
    intro h
    rw [h]
  ·
    intro h
    simp [List.Vector.toList] at h
    apply Eq.of.Val h


-- created on 2025-05-11
-- updated on 2026-09-09
