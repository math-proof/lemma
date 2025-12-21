import Lemma.Hyperreal.NotInfinitesimalAdd.of.Ge_0.Gt_0
import Lemma.Nat.Add
open Hyperreal Nat


@[main]
private lemma main
  {r : ℝ}
  {x : ℝ*}
-- given
  (h_r : r > 0)
  (h : x ≥ 0) :
-- imply
  ¬Infinitesimal (r + x) := by
-- proof
  rw [Add.comm]
  apply NotInfinitesimalAdd.of.Ge_0.Gt_0
  repeat assumption


-- created on 2025-12-21
