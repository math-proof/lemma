import sympy.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Bounds.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Real.Sup.eq.Min |
| comm | Real.Min.eq.Sup |
-/
@[main, comm]
private lemma main
  {α : Type*} [ConditionallyCompleteLinearOrder α] [DenselyOrdered α]
  {f : α → α}
  {m M : α}
-- given
  (hm : m < M)
  (hb : BddAbove (f '' Set.Ioo m M)) :
-- imply
  sSup (f '' Set.Ioo m M) = sInf (upperBounds (f '' Set.Ioo m M)) :=
-- proof
  have hine : (f '' Set.Ioo m M).Nonempty := (Set.nonempty_Ioo.mpr hm).image _
  have hub_ne : (upperBounds (f '' Set.Ioo m M)).Nonempty := hb
  have hub : BddBelow (upperBounds (f '' Set.Ioo m M)) :=
    hine.mono (subset_lowerBounds_upperBounds _)
  ((isGLB_csInf hub_ne hub).unique (isLUB_csSup hine hb).isGLB).symm


-- created on 2019-01-15
