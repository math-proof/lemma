import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.Pressure.Part2
open Finset StatMech StatMech.Onsager


/--
[ons_X_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/Pressure.lean)
-/
@[path]
private lemma ons_X_pos_eq
  [Fintype V]
  [DecidableEq V]
  {x : ℝ}
-- given
  (hx : 0 ≤ x) :
-- imply
  0 < ons_X G x := by
-- proof
  apply StatMech.Onsager.ons_X_pos x hx

/--
[ons_pressureFinite_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/Pressure.lean)
-/
@[path]
private lemma ons_pressureFinite_eq_eq
  [Fintype V]
  [DecidableEq V]
  {β : ℝ}
-- given
  (hβ : 0 ≤ β)
  (hV : 0 < Fintype.card V) :
-- imply
  ons_pressureFinite G β = Real.log 2 + (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ) * Real.log (Real.cosh β) + Real.log (ons_X G (Real.tanh β)) / (Fintype.card V : ℝ) := by
-- proof
  apply StatMech.Onsager.ons_pressureFinite_eq β hβ hV


-- created on 2026-10-23
