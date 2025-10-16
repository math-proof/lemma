import Lemma.Algebra.Min.eq.IteLe
import Lemma.Algebra.Ite.eq.SubIte
import Lemma.Algebra.Min
open Algebra


@[main, comm]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
-- given
  (a b d : α) :
-- imply
  a ⊓ b - d = (a - d) ⊓ (b - d) := by
-- proof
  repeat rw [Min.eq.IteLe]
  simp [SubIte.eq.Ite]


-- created on 2025-07-18
-- updated on 2025-10-16
