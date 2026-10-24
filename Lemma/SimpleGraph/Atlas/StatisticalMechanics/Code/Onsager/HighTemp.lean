import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.HighTemp
open Finset StatMech StatMech.Onsager


/--
[ons_hte](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/HighTemp.lean)
-/
@[path]
private lemma ons_hte_eq
  [Fintype V]
  [DecidableEq V]
  {β : ℝ} :
-- imply
  ons_Z G β = (2 : ℝ) ^ Fintype.card V * (Real.cosh β) ^ G.edgeFinset.card * ons_X G (Real.tanh β) := by
-- proof
  apply StatMech.Onsager.ons_hte β


-- created on 2026-10-23
