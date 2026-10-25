import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentLaw.Part3
open MeasureTheory StatMech StatMech.FrontierB


/--
[currentSummand_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentLaw.lean)
-/
@[path]
private lemma currentSummand_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
  {m : EdgeCurrent G}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ if sources G (ofEdgeFun G m) = A then weight G beta J (ofEdgeFun G m) else 0 := by
-- proof
  apply StatMech.FrontierB.currentSummand_nonneg G beta J hbeta hJ A m

/--
[tsum_currentRawMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentLaw.lean)
-/
@[path]
private lemma tsum_currentRawMass_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  ∑' m : EdgeCurrent G, currentRawMass G beta J A m = ENNReal.ofReal (currentSum G beta J A) := by
-- proof
  apply StatMech.FrontierB.tsum_currentRawMass G beta J hbeta hJ A

/--
[currentPMF_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentLaw.lean)
-/
@[path]
private lemma currentPMF_apply_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
  {m : EdgeCurrent G}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e)
  (hA : 0 < currentSum G beta J A) :
-- imply
  currentPMF G beta J hbeta hJ A hA m = currentRawMass G beta J A m * (ENNReal.ofReal (currentSum G beta J A))⁻¹ := by
-- proof
  apply StatMech.FrontierB.currentPMF_apply G beta J hbeta hJ A hA m

/--
[currentPMF_apply_eq_zero_of_sources_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentLaw.lean)
-/
@[path]
private lemma currentPMF_apply_eq_zero_of_sources_ne_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
  {m : EdgeCurrent G}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e)
  (hA : 0 < currentSum G beta J A)
  (hm : sources G (ofEdgeFun G m) ≠ A) :
-- imply
  currentPMF G beta J hbeta hJ A hA m = 0 := by
-- proof
  apply StatMech.FrontierB.currentPMF_apply_eq_zero_of_sources_ne G beta J hbeta hJ A hA m hm

/--
[sourcelessCurrentMeasure_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentLaw.lean)
-/
@[path]
private lemma sourcelessCurrentMeasure_singleton_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {m : EdgeCurrent G}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  (sourcelessCurrentMeasure G beta J hbeta hJ : Measure (EdgeCurrent G)) {m} = sourcelessCurrentPMF G beta J hbeta hJ m := by
-- proof
  apply StatMech.FrontierB.sourcelessCurrentMeasure_singleton G beta J hbeta hJ m

/--
[sourcelessCurrentMeasure_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentLaw.lean)
-/
@[path]
private lemma sourcelessCurrentMeasure_sources_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  (sourcelessCurrentMeasure G beta J hbeta hJ : Measure (EdgeCurrent G)) {m | sources G (ofEdgeFun G m) = ∅} = 1 := by
-- proof
  apply StatMech.FrontierB.sourcelessCurrentMeasure_sources G beta J hbeta hJ


-- created on 2026-10-23
