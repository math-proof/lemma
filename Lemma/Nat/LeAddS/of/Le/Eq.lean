import Lemma.Nat.LeAddS.is.Le
open Nat


/--
| attributes | lemma |
| :---: | :---: |
| path | Nat.LeAddS.of.Le.Eq |
| comm 3 | Nat.GeAddS.of.Ge.Eq |
-/
@[path, comm 3]
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


-- created on 2018-10-29
