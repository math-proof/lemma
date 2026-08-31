import Lemma.Set.In_Finset.is.OrEqS
import Lemma.Set.In_Insert.is.Eq.ou.In
open Set


/--
| attributes | lemma |
| :---: | :---: |
| main | Set.In_Finset.is.Or_OrEqS |
| comm | Set.Or_OrEqS.is.In_Finset |
| mp | Set.Or_OrEqS.of.In_Finset |
| mpr | Set.In_Finset.of.Or_OrEqS |
-/
@[main, comm, mp, mpr]
private lemma main
-- given
  (a b c e : α) :
-- imply
  e ∈ ({a, b, c} : Set α) ↔ e = a ∨ e = b ∨ e = c := by
-- proof
  rw [In_Insert.is.Eq.ou.In, In_Finset.is.OrEqS]


-- created on 2026-08-31
