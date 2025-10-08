import Lemma.Algebra.Eq_AddMulDiv___Mod
import Lemma.Nat.EqCoeS.is.Eq
import Lemma.Algebra.EqModS.of.Eq
import Lemma.Algebra.EqMod
open Algebra Nat


@[main]
private lemma main
  {k n m : ℕ}
  {i : Fin m}
  {j : Fin n}
-- given
  (h_eq : k = i * n + j) :
-- imply
  j = k % n := by
-- proof
  have := Eq_AddMulDiv___Mod k n
  have := h_eq.symm.trans this
  have h_mod := EqModS.of.Eq this n
  have h_mod := EqCoeS.of.Eq (R := ℤ) h_mod
  simp at h_mod
  norm_cast at h_mod
  rwa [EqMod] at h_mod


-- created on 2025-07-07
