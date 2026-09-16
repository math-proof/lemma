import sympy.vector.Basic
import Lemma.Vector.Repeat0.eq.Zero
import Lemma.Vector.EqAppend0S0
import Lemma.Vector.EqCast_0'0.of.Eq
import Lemma.Nat.EqAddMulDiv
open Vector


@[main]
private lemma main
  [Zero α]
-- given
  (n n' : ℕ) :
-- imply
  (0 : List.Vector α n).resize n' = 0 := by
-- proof
  simp [List.Vector.resize, Repeat0.eq.Zero, EqAppend0S0]
  rw [EqCast_0'0.of.Eq (Nat.EqAddMulDiv n' n)]


-- created on 2026-09-16
