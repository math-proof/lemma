import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierB.FiniteBoundarySourceLaw
open MeasureTheory StatMech StatMech.FrontierB


/--
[boundarySourceCurrentSummand_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoundarySourceLaw.lean)
-/
@[path]
private lemma boundarySourceCurrentSummand_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {interior internalSources : Finset V}
  {m : EdgeCurrent G}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ if sources G (ofEdgeFun G m) ∩ interior = internalSources then weight G beta J (ofEdgeFun G m) else 0 := by
-- proof
  apply StatMech.FrontierB.boundarySourceCurrentSummand_nonneg G beta J hbeta hJ interior internalSources m

/--
[summable_boundarySourceCurrentSummand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoundarySourceLaw.lean)
-/
@[path]
private lemma summable_boundarySourceCurrentSummand_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {interior internalSources : Finset V} :
-- imply
  Summable (fun m : EdgeCurrent G => if sources G (ofEdgeFun G m) ∩ interior = internalSources then weight G beta J (ofEdgeFun G m) else 0) := by
-- proof
  apply StatMech.FrontierB.summable_boundarySourceCurrentSummand G beta J interior internalSources

/--
[tsum_boundarySourceCurrentRawMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoundarySourceLaw.lean)
-/
@[path]
private lemma tsum_boundarySourceCurrentRawMass_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {interior internalSources : Finset V}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  ∑' m : EdgeCurrent G, boundarySourceCurrentRawMass G beta J interior internalSources m = ENNReal.ofReal (boundarySourceCurrentSum G beta J interior internalSources) := by
-- proof
  apply StatMech.FrontierB.tsum_boundarySourceCurrentRawMass G beta J hbeta hJ interior internalSources

/--
[boundarySourceCurrentPMF_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoundarySourceLaw.lean)
-/
@[path]
private lemma boundarySourceCurrentPMF_apply_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {interior internalSources : Finset V}
  {m : EdgeCurrent G}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e)
  (hpos : 0 < boundarySourceCurrentSum G beta J interior internalSources) :
-- imply
  boundarySourceCurrentPMF G beta J hbeta hJ interior internalSources hpos m = boundarySourceCurrentRawMass G beta J interior internalSources m * (ENNReal.ofReal (boundarySourceCurrentSum G beta J interior internalSources))⁻¹ := by
-- proof
  apply StatMech.FrontierB.boundarySourceCurrentPMF_apply G beta J hbeta hJ interior internalSources hpos m

/--
[boundarySourceCurrentPairPMF_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoundarySourceLaw.lean)
-/
@[path]
private lemma boundarySourceCurrentPairPMF_apply_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {interior internalSources exactSecondSources : Finset V}
  {m n : EdgeCurrent G}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e)
  (hfirst : 0 < boundarySourceCurrentSum G beta J interior internalSources)
  (hsecond : 0 < currentSum G beta J exactSecondSources) :
-- imply
  boundarySourceCurrentPairPMF G beta J hbeta hJ interior internalSources exactSecondSources hfirst hsecond (m, n) = boundarySourceCurrentPMF G beta J hbeta hJ interior internalSources hfirst m * currentPMF G beta J hbeta hJ exactSecondSources hsecond n := by
-- proof
  apply StatMech.FrontierB.boundarySourceCurrentPairPMF_apply G beta J hbeta hJ interior internalSources exactSecondSources hfirst hsecond m n

/--
[boundarySourceCurrentPairPMF_toMeasure_eq_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoundarySourceLaw.lean)
-/
@[path]
private lemma boundarySourceCurrentPairPMF_toMeasure_eq_prod_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {interior internalSources exactSecondSources : Finset V}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e)
  (hfirst : 0 < boundarySourceCurrentSum G beta J interior internalSources)
  (hsecond : 0 < currentSum G beta J exactSecondSources) :
-- imply
  (boundarySourceCurrentPairPMF G beta J hbeta hJ interior internalSources exactSecondSources hfirst hsecond).toMeasure = (boundarySourceCurrentPMF G beta J hbeta hJ interior internalSources hfirst).toMeasure.prod (currentPMF G beta J hbeta hJ exactSecondSources hsecond).toMeasure := by
-- proof
  apply StatMech.FrontierB.boundarySourceCurrentPairPMF_toMeasure_eq_prod G beta J hbeta hJ interior internalSources exactSecondSources hfirst hsecond

/--
[boundarySourceCurrentPairPMF_superpositionEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoundarySourceLaw.lean)
-/
@[path]
private lemma boundarySourceCurrentPairPMF_superpositionEvent_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {interior internalSources exactSecondSources : Finset V}
  [DecidablePred P]
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e)
  (hfirst : 0 < boundarySourceCurrentSum G beta J interior internalSources)
  (hsecond : 0 < currentSum G beta J exactSecondSources)
  (P : Current V → Prop) :
-- imply
  (boundarySourceCurrentPairPMF G beta J hbeta hJ interior internalSources exactSecondSources hfirst hsecond).toMeasure (sourcePairSuperpositionEvent G P) = ENNReal.ofReal (boundarySourceGatedPairSum G beta J interior internalSources exactSecondSources P / (boundarySourceCurrentSum G beta J interior internalSources * currentSum G beta J exactSecondSources)) := by
-- proof
  apply StatMech.FrontierB.boundarySourceCurrentPairPMF_superpositionEvent G beta J hbeta hJ interior internalSources exactSecondSources hfirst hsecond P

/--
[boundarySourceCurrentPairPMF_switching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoundarySourceLaw.lean)
-/
@[path]
private lemma boundarySourceCurrentPairPMF_switching_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {interior : Finset V}
  {u v : V}
  [DecidablePred P]
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e)
  (huv : u ≠ v)
  (hu : u ∈ interior)
  (hv : v ∈ interior)
  (P : Current V → Prop)
  (hBoundaryPair : 0 < boundarySourceCurrentSum G beta J interior {u, v})
  (hPair : 0 < currentSum G beta J {u, v})
  (hBoundaryZero : 0 < boundarySourceCurrentSum G beta J interior ∅)
  (hZero : 0 < currentSum G beta J ∅) :
-- imply
  ENNReal.ofReal (boundarySourceCurrentSum G beta J interior {u, v} * currentSum G beta J {u, v}) * (boundarySourceCurrentPairPMF G beta J hbeta hJ interior {u, v} {u, v} hBoundaryPair hPair).toMeasure (sourcePairSuperpositionEvent G P) = ENNReal.ofReal (boundarySourceCurrentSum G beta J interior ∅ * currentSum G beta J ∅) * (boundarySourceCurrentPairPMF G beta J hbeta hJ interior ∅ ∅ hBoundaryZero hZero).toMeasure (sourcePairSuperpositionEvent G (fun m => P m ∧ CurrentConnected G m u v)) := by
-- proof
  apply StatMech.FrontierB.boundarySourceCurrentPairPMF_switching G beta J hbeta hJ interior huv hu hv P hBoundaryPair hPair hBoundaryZero hZero


-- created on 2026-10-23
