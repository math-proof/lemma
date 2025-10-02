import sympy.vector.vector
import Lemma.Algebra.Get_Add.eq.Get.of.Val.eq.ValAppend.of.Lt.LtAdd
import Lemma.Algebra.EqValS.of.Eq
open Algebra


@[main]
private lemma main
  {a : List.Vector α N}
  {b : List.Vector α m}
  {c : List.Vector α n}
-- given
  (h₀ : m + i < N)
  (h₁ : i < n)
  (h₂ : a ≃ b ++ c) :
-- imply
  a[m + i] = c[i] := by
-- proof
  apply Get_Add.eq.Get.of.Val.eq.ValAppend.of.Lt.LtAdd h₀ h₁
  apply EqValS.of.Eq h₂


-- created on 2025-06-04
