import Lemma.Hyperreal.NotInfinitesimal.is.Any_GeAbs
import Lemma.Nat.LtAddS.of.Le.Lt
import Lemma.Int.EqAbs.is.Ge_0
import Lemma.Real.LtCoeS.is.Lt
open Hyperreal Int Nat Real


@[main]
private lemma main
  {x : ℝ*}
  {r : ℝ}
-- given
  (h : x ≥ 0)
  (h_r : r > 0) :
-- imply
  ¬Infinitesimal (x + r) := by
-- proof
  apply NotInfinitesimal.of.Any_GeAbs
  use ⟨r, h_r⟩
  simp
  rw [EqAbs.of.Ge_0]
  .
    linarith
  .
    have := GtAddS.of.Ge.Gt h (Real.GtCoeS.of.Gt h_r)
    simp_all
    linarith


-- created on 2025-12-20
