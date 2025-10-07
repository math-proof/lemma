import Lemma.Bool.Bool.eq.Ite
open Bool


@[main, comm, mp, mpr]
private lemma main
  [Decidable p] :
-- imply
  p ↔ Bool.toNat p = 1 := by
-- proof
  rw [Bool.eq.Ite]
  simp


-- created on 2025-04-20
