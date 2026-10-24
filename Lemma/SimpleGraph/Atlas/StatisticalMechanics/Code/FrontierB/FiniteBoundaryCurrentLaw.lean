import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierB.FiniteBoundaryCurrentLaw
open MeasureTheory StatMech StatMech.FrontierB


/--
[boundaryCurrentSummand_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoundaryCurrentLaw.lean)
-/
@[path]
private lemma boundaryCurrentSummand_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {interior : Finset V}
  {m : EdgeCurrent G}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ if (sources G (ofEdgeFun G m)) ∩ interior = ∅ then weight G beta J (ofEdgeFun G m) else 0 := by
-- proof
  apply StatMech.FrontierB.boundaryCurrentSummand_nonneg G beta J hbeta hJ interior m

/--
[summable_boundaryCurrentSummand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoundaryCurrentLaw.lean)
-/
@[path]
private lemma summable_boundaryCurrentSummand_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {interior : Finset V} :
-- imply
  Summable (fun m : EdgeCurrent G => if (sources G (ofEdgeFun G m)) ∩ interior = ∅ then weight G beta J (ofEdgeFun G m) else 0) := by
-- proof
  apply StatMech.FrontierB.summable_boundaryCurrentSummand G beta J interior

/--
[tsum_boundaryCurrentRawMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoundaryCurrentLaw.lean)
-/
@[path]
private lemma tsum_boundaryCurrentRawMass_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {interior : Finset V}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  ∑' m : EdgeCurrent G, boundaryCurrentRawMass G beta J interior m = ENNReal.ofReal (boundaryCurrentSum G beta J interior) := by
-- proof
  apply StatMech.FrontierB.tsum_boundaryCurrentRawMass G beta J hbeta hJ interior

/--
[one_le_boundaryCurrentSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoundaryCurrentLaw.lean)
-/
@[path]
private lemma one_le_boundaryCurrentSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {interior : Finset V}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  1 ≤ boundaryCurrentSum G beta J interior := by
-- proof
  apply StatMech.FrontierB.one_le_boundaryCurrentSum G beta J hbeta hJ interior

/--
[boundaryCurrentPMF_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoundaryCurrentLaw.lean)
-/
@[path]
private lemma boundaryCurrentPMF_apply_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {interior : Finset V}
  {m : EdgeCurrent G}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  boundaryCurrentPMF G beta J hbeta hJ interior m = boundaryCurrentRawMass G beta J interior m * (ENNReal.ofReal (boundaryCurrentSum G beta J interior))⁻¹ := by
-- proof
  apply StatMech.FrontierB.boundaryCurrentPMF_apply G beta J hbeta hJ interior m

/--
[boundaryCurrentMeasure_sources_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoundaryCurrentLaw.lean)
-/
@[path]
private lemma boundaryCurrentMeasure_sources_interior_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {interior : Finset V}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  (boundaryCurrentMeasure G beta J hbeta hJ interior : Measure (EdgeCurrent G)) {m | (sources G (ofEdgeFun G m)) ∩ interior = ∅} = 1 := by
-- proof
  apply StatMech.FrontierB.boundaryCurrentMeasure_sources_interior G beta J hbeta hJ interior


-- created on 2026-10-23
