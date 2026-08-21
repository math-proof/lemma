import Lemma.Set.Cup_Ico.eq.Ioc.of.Lt
import Lemma.Set.Ioc.eq.Empty.of.Ge
import Lemma.Set.Ico.eq.Empty.of.Ge
open Set


/--
| attributes | lemma |
| :---: | :---: |
| main | Set.Cup_Ioc.eq.Ioc |
| comm | Set.Ioc.eq.Cup_Ioc |
-/
@[main, comm]
private lemma main
  [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
  {a b : ℤ} :
-- imply
  ⋃ k ∈ Ico a b, Ioc (k : R) (k + 1 : R) = Ioc (a : R) (b : R) := by
-- proof
  by_cases h : a < b
  ·
    exact Cup_Ico.eq.Ioc.of.Lt h
  ·
    have hge : a ≥ b := le_of_not_gt h
    rw [Ico.eq.Empty.of.Ge hge]
    simpa using (Ioc.eq.Empty.of.Ge (x := (a : R)) (y := (b : R)) (Int.cast_le.mpr hge)).symm


-- created on 2018-10-20
-- updated on 2026-08-21
