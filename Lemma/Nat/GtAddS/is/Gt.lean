import Lemma.Nat.LtAddS.is.Lt
open Nat


@[main, comm, mp 4, mpr 8]
private lemma left
  [Add α]
  [LT α]
  [AddLeftStrictMono α]
  [AddLeftReflectLT α]
-- given
  (a b c : α) :
-- imply
  a + b > a + c ↔ b > c :=
-- proof
  ⟨Lt.of.LtAddS.left, (LtAddS.of.Lt.left a ·)⟩


@[main, comm, mp 4, mpr 8]
private lemma main
  [Add α]
  [LT α]
  [AddRightStrictMono α]
  [AddRightReflectLT α]
-- given
  (a b c : α) :
-- imply
  b + a > c + a ↔ b > c:=
-- proof
  ⟨Lt.of.LtAddS, (LtAddS.of.Lt a ·)⟩


-- created on 2024-07-01
-- updated on 2025-08-02
