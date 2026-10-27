import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusWiredCutLimit
open MeasureTheory Filter Topology StatMech StatMech.Onsager


/--
[plusWiredCutRatio_tendsto_plusState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusWiredCutLimit.lean)
-/
@[path]
private lemma plusWiredCutRatio_tendsto_plusState_eq
  {d : Nat}
  {beta : Real}
  {u v : Site d}
  {path : (hypercubicLattice d).Walk u v}
-- given
  (hbeta : 0 ≤ beta)
  (huv : u ≠ v) :
-- imply
  Tendsto (fun n => ons_plusWiredPathNumerator d n beta u v / ons_plusWiredContourDenominator d n beta) atTop (nhds (∫ config, spin config u * spin config v ∂(plusState d beta 0 : Measure (ConfigSpace (Site d))))) := by
-- proof
  apply StatMech.Onsager.plusWiredCutRatio_tendsto_plusState d beta hbeta huv path


-- created on 2026-10-23
