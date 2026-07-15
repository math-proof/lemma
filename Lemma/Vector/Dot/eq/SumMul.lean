import Lemma.Nat.EqMax
import Lemma.Vector.EqResize
open Nat Vector


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (a b : List.Vector α n) :
-- imply
  a @ b = (a * b).sum := by
-- proof
  dsimp only [Dot.dot]
  rw [EqMax]
  rw [EqResize a, EqResize b]


-- created on 2026-07-15
