import Lemma.Fin.EqOfSplitToSplit
import Lemma.Fin.EqToSplitOfSplit
import Lemma.Fin.OfSplit.eq.Ite_Mul2
import Lemma.Fin.ToSplit.eq.Ite_Div_2
import Lemma.Nat.Delta.eq.Ite
import sympy.functions.special.tensor_functions
open Nat Fin


@[main]
private lemma main
-- given
  (k j : Fin (d + d)) :
-- imply
  KroneckerDelta (j : ℕ) k.ofSplit = KroneckerDelta (k : ℕ) j.toSplit := by
-- proof
  rw [Delta.eq.Ite, Delta.eq.Ite]
  congr 1
  apply propext
  constructor
  ·
    intro h
    have hj : j = k.ofSplit := Fin.ext h
    have hinv := EqToSplitOfSplit k
    have := congrArg toSplit hj
    rw [hinv] at this
    apply congrArg Fin.val this.symm
  ·
    intro h
    have hk : k = j.toSplit := Fin.ext h
    have hinv := EqOfSplitToSplit j
    have := congrArg ofSplit hk
    rw [hinv] at this
    apply congrArg Fin.val this.symm


-- created on 2026-09-05
