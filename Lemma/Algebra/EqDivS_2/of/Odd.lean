import sympy.functions.elementary.integers
import Lemma.Nat.EqSubAdd
import Lemma.Algebra.EqDivMul.of.Ne_0
import Lemma.Algebra.Eq_AddMulDiv___Mod
import Lemma.Algebra.ModAddMul.eq.Mod
import Lemma.Algebra.EqDivS.of.Eq
import Lemma.Algebra.EqMod.of.Lt.Ge_0
import Lemma.Algebra.Odd.is.Any_Eq_AddMul2
open Algebra Nat


@[main, comm]
private lemma main
  [IntegerRing Z]
  {n : Z}
-- given
  (h : n is odd) :
-- imply
  (n - 1) / 2 = n / 2 := by
-- proof
  obtain ⟨k, hk⟩ := Any_Eq_AddMul2.of.Odd h
  rw [hk]
  rw [EqSubAdd]
  rw [EqDivMul.of.Ne_0.left (by norm_num)]
  have h := Eq_AddMulDiv___Mod (2 * k + 1) 2
  rw [ModAddMul.eq.Mod.left] at h
  rw [EqMod.of.Lt.Ge_0 (by simp) (by simp)] at h
  simp at h
  have h := EqDivS.of.Eq h 2
  rw [EqDivMul.of.Ne_0.left (by norm_num)] at h
  rwa [EqDivMul.of.Ne_0 (by norm_num)] at h


-- created on 2025-08-12
-- updated on 2025-08-13
