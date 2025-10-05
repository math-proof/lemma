import sympy.vector.vector
import Lemma.Vector.EqGetS.of.Val.eq.ValAppend.of.Lt.Lt
import Lemma.Vector.EqValS.of.SEq
open Vector


@[main]
private lemma main
  {a : List.Vector α N}
  {b : List.Vector α m}
  {c : List.Vector α n}
-- given
  (h₀ : i < N)
  (h₁ : i < m)
  (h₂ : a ≃ b ++ c) :
-- imply
  a[i] = b[i] := by
-- proof
  apply EqGetS.of.Val.eq.ValAppend.of.Lt.Lt h₀ h₁
  apply EqValS.of.SEq h₂


-- created on 2025-06-04
