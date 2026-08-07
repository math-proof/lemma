import Lemma.Nat.LeAddS.is.Le
open Nat


/--
| attributes | lemma |
| :---: | :---: |
| main | Nat.LeAddS.of.Le.Eq |
| comm 3 | Nat.GeAddS.of.Ge.Eq |
-/
@[main, comm 3]
private lemma main
  [Add α]
  [Preorder α]
  [AddRightMono α]
  {a x b y : α}
-- given
  (h₀ : y ≤ b)
  (h₁ : a = x) :
-- imply
  y + a ≤ b + x := by
-- proof
  rw [← h₁]
  exact LeAddS.of.Le a h₀


-- created on 2018-09-01
