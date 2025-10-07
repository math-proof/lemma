import Lemma.Bool.Bool.eq.Ite
import Lemma.Logic.BFn_Ite.is.OrAndS
open Logic Bool


@[main]
private lemma main
  [Decidable p]
-- given
  (h : Bool.toNat p ≠ 1) :
-- imply
  Bool.toNat p = 0 := by
-- proof
  rw [Bool.eq.Ite] at h
  have h := h.symm
  rw [BFn_Ite.is.OrAndS (R := Ne)] at h
  simp at h
  rw [Bool.eq.Ite]
  apply Eq.symm
  rw [BFn_Ite.is.OrAndS (R := Eq)]
  simp [h]


-- created on 2025-04-11
