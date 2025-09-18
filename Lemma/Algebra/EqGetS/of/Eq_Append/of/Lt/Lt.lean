import stdlib.List.Vector
import Lemma.Algebra.EqGetS.of.Val.eq.ValAppend.of.Lt.Lt
import Lemma.Algebra.EqValS.of.Eq
open Algebra


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
  apply EqValS.of.Eq h₂


-- created on 2025-06-04
