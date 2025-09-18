import Lemma.Algebra.LeAddS.is.Le
open Algebra


@[main, comm, mp 8, mpr 4]
private lemma left
  [Add α]
  [LE α]
  [AddLeftReflectLE α]
  [AddLeftMono α]
-- given
  (a b c : α) :
-- imply
  a + b ≥ a + c ↔ b ≥ c :=
-- proof
  ⟨Le.of.LeAddS.left, (LeAddS.of.Le.left a ·)⟩


@[main, comm, mp 8, mpr 4]
private lemma main
  [Add α]
  [LE α]
  [AddRightReflectLE α]
  [AddRightMono α]
-- given
  (a b c : α) :
-- imply
  b + a ≥ c + a ↔ b ≥ c :=
-- proof
  ⟨Le.of.LeAddS, (LeAddS.of.Le a ·)⟩


-- created on 2024-07-01
-- updated on 2025-08-02
