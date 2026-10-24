import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.SignedLoopLowTempPlusLimit
open MeasureTheory Filter Topology BoundedContinuousFunction StatMech StatMech.Onsager


/--
[plusLowTempPathRatio_tendsto_plusState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempPlusLimit.lean)
-/
@[path]
private lemma plusLowTempPathRatio_tendsto_plusState_eq
  {d : Nat}
  {beta : Real}
  {u v : Site d}
  {path : (hypercubicLattice d).Walk u v}
-- given
  (hbeta : 0 ≤ beta)
  (huv : u ≠ v) :
-- imply
  Tendsto (fun n => ons_plusLowTempPathNumerator d n beta path / ons_plusLowTempContourDenominator d n beta) atTop (nhds (∫ config, spin config u * spin config v ∂(plusState d beta 0 : Measure (ConfigSpace (Site d))))) := by
-- proof
  apply StatMech.Onsager.plusLowTempPathRatio_tendsto_plusState d beta hbeta huv path


-- created on 2026-10-23
