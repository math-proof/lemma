import Lemma.Set.Any_In.is.Ne_Empty
import Lemma.Nat.Lt.of.Le.Lt
open Set Nat


/--
| attributes | lemma |
| :---: | :---: |
| main | Set.Lt.of.Ico.ne.Empty |
| comm | Set.Gt.of.Ico.ne.Empty |
-/
@[main, comm]
private lemma main
  [Preorder α]
  {a b : α}
-- given
  (h : Ico a b ≠ ∅) :
-- imply
  a < b := by
-- proof
  let ⟨e, h_e⟩ := Any_In.of.Ne_Empty h
  apply Lt.of.Le.Lt h_e.left h_e.right


-- created on 2018-10-19
