import Lemma.Set.Any_In.is.Ne_Empty
import Lemma.Nat.Lt.of.Lt.Le
open Set Nat


/--
| attributes | lemma |
| :---: | :---: |
| main | Set.Lt.of.Ioc.ne.Empty |
| comm | Set.Gt.of.Ioc.ne.Empty |
-/
@[main, comm]
private lemma main
  [Preorder α]
  {a b : α}
-- given
  (h : Ioc a b ≠ ∅) :
-- imply
  a < b := by
-- proof
  let ⟨e, h_e⟩ := Any_In.of.Ne_Empty h
  apply Lt.of.Lt.Le h_e.left h_e.right


-- created on 2018-10-16
-- updated on 2026-08-18
