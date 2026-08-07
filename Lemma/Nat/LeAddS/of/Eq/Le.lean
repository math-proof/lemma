import Lemma.Nat.LeAddS.is.Le
open Nat


/--
| attributes | lemma |
| :---: | :---: |
| main | Nat.LeAddS.of.Eq.Le |
| comm 3 | Nat.GeAddS.of.Eq.Ge |
-/
@[main, comm 3]
private lemma main
  [Add α]
  [Preorder α]
  [AddLeftMono α]
  {a x b y : α}
-- given
  (h₀ : a = x)
  (h₁ : y ≤ b) :
-- imply
  a + y ≤ x + b := by
-- proof
  rw [h₀]
  exact LeAddS.of.Le.left x h₁


-- created on 2018-09-01
