import sympy.tensor.Basic
import Lemma.Tensor.Eq.is.EqDataS
open Tensor


@[main, comm, mp, mpr]
private lemma main
-- given
  (A B : Tensor α []) :
-- imply
  A = B ↔ A.item = B.item := by
-- proof
  constructor
  · intro h
    rw [h]
  · intro h
    apply Eq.of.EqDataS
    ext i
    have : i = ⟨0, Nat.zero_lt_one⟩ := Fin.ext (Nat.lt_one_iff.mp i.isLt)
    subst this
    exact h


-- created on 2026-09-07
