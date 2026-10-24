import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.osd_logstep
open Real StatMech StatMech.Walls


/--
[osd_logStep_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/osd_logstep.lean)
-/
@[path]
private lemma osd_logStep_le_eq
  {S f : ℝ}
-- given
  (hS : 0 < S)
  (hf : 0 ≤ f) :
-- imply
  Real.log (S + f) - Real.log S ≤ f / S := by
-- proof
  apply StatMech.Walls.osd_logStep_le S f hS hf

/--
[osd_logStep_telescope](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/osd_logstep.lean)
-/
@[path]
private lemma osd_logStep_telescope_eq
  {Sig Signext fi : ℝ}
-- given
  (hSpos : 0 < Sig)
  (hfnn : 0 ≤ fi)
  (hrec : Signext = Sig + fi) :
-- imply
  Real.log Signext - Real.log Sig ≤ fi / Sig := by
-- proof
  apply StatMech.Walls.osd_logStep_telescope Sig Signext fi hSpos hfnn hrec

/--
[osd_logStep_le_eq_integration](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/osd_logstep.lean)
-/
@[path]
private lemma osd_logStep_le_eq_integration_eq :
-- imply
  (@osd_logStep_le) = (@StatMech.OSSS.Integration.logStep_le) := by
-- proof
  apply StatMech.Walls.osd_logStep_le_eq_integration


-- created on 2026-10-23
