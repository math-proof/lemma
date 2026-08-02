import sympy.sets.sets
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Set.In_Icc.is.InNeg |
| comm | Set.InNeg.is.In_Icc |
| mp | Set.InNeg.of.In_Icc |
| mpr | Set.In_Icc.of.InNeg |
| mp.mt | Set.NotIn_Icc.of.NotInNeg |
| mpr.mt | Set.NotInNeg.of.NotIn_Icc |
-/
@[main, comm, mp, mpr, mp.mt, mpr.mt]
private lemma main
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
-- given
  (x a b : α) :
-- imply
  x ∈ Icc a b ↔ -x ∈ Icc (-b) (-a) := by
-- proof
  aesop


-- created on 2018-10-06
