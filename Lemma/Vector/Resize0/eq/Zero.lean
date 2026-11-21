import Lemma.Vector.Repeat0.eq.Zero
import Lemma.Vector.EqAppend0S0
import Lemma.Vector.EqCast_0'0.of.Eq
open Vector


@[path]
private lemma main
  [Zero α]
-- given
  (n n' : ℕ) :
-- imply
  (0 : List.Vector α n).resize n' = 0 := by
-- proof
  simp only [List.Vector.resize, Repeat0.eq.Zero]
  change cast _ ((0 : List.Vector α (n' / n * n)) ++ (0 : List.Vector α (n' % n))) = 0
  rw [EqAppend0S0, EqCast_0'0.of.Eq (Nat.EqAddMulDiv n' n)]


-- created on 2026-09-16
-- updated on 2026-11-20
