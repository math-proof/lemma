import Lemma.Bool.Bool.eq.Ite
open Bool


@[path]
private lemma main
  [Decidable p]
-- given
  (h : p) :
-- imply
  Bool.toNat p = 1 := by
-- proof
  rw [Bool.eq.Ite]
  simp [h]


-- created on 2018-02-16
