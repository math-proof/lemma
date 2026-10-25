import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentPairLaw.Part2
open MeasureTheory StatMech StatMech.FrontierB


/--
[sourceCurrentPairPMF_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentPairLaw.lean)
-/
@[path]
private lemma sourceCurrentPairPMF_apply_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {A B : Finset V}
  {m n : EdgeCurrent G}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e)
  (hA : 0 < currentSum G beta J A)
  (hB : 0 < currentSum G beta J B) :
-- imply
  sourceCurrentPairPMF G beta J hbeta hJ A B hA hB (m, n) = currentPMF G beta J hbeta hJ A hA m * currentPMF G beta J hbeta hJ B hB n := by
-- proof
  apply StatMech.FrontierB.sourceCurrentPairPMF_apply G beta J hbeta hJ A B hA hB m n

/--
[sourceCurrentPairPMF_toMeasure_eq_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentPairLaw.lean)
-/
@[path]
private lemma sourceCurrentPairPMF_toMeasure_eq_prod_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {A B : Finset V}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e)
  (hA : 0 < currentSum G beta J A)
  (hB : 0 < currentSum G beta J B) :
-- imply
  (sourceCurrentPairPMF G beta J hbeta hJ A B hA hB).toMeasure = (currentPMF G beta J hbeta hJ A hA).toMeasure.prod (currentPMF G beta J hbeta hJ B hB).toMeasure := by
-- proof
  apply StatMech.FrontierB.sourceCurrentPairPMF_toMeasure_eq_prod G beta J hbeta hJ A B hA hB

/--
[sourceCurrentPairPMF_superpositionEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentPairLaw.lean)
-/
@[path]
private lemma sourceCurrentPairPMF_superpositionEvent_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {A B : Finset V}
  [DecidablePred P]
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e)
  (hA : 0 < currentSum G beta J A)
  (hB : 0 < currentSum G beta J B)
  (P : Current V → Prop) :
-- imply
  (sourceCurrentPairPMF G beta J hbeta hJ A B hA hB).toMeasure (sourcePairSuperpositionEvent G P) = ENNReal.ofReal (normalizedGatedSourcePairSum G beta J A B P) := by
-- proof
  apply StatMech.FrontierB.sourceCurrentPairPMF_superpositionEvent G beta J hbeta hJ A B hA hB P

/--
[sourceCurrentPairPMF_switching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentPairLaw.lean)
-/
@[path]
private lemma sourceCurrentPairPMF_switching_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
  {u v : V}
  [DecidablePred P]
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e)
  (huv : u ≠ v)
  (P : Current V → Prop)
  (hAu : 0 < currentSum G beta J (A ∆ ({u, v} : Finset V)))
  (huvSum : 0 < currentSum G beta J ({u, v} : Finset V))
  (hA : 0 < currentSum G beta J A)
  (hzero : 0 < currentSum G beta J ∅) :
-- imply
  ENNReal.ofReal (currentSum G beta J (A ∆ ({u, v} : Finset V)) * currentSum G beta J ({u, v} : Finset V)) * (sourceCurrentPairPMF G beta J hbeta hJ (A ∆ ({u, v} : Finset V)) {u, v} hAu huvSum).toMeasure (sourcePairSuperpositionEvent G P) = ENNReal.ofReal (currentSum G beta J A * currentSum G beta J ∅) * (sourceCurrentPairPMF G beta J hbeta hJ A ∅ hA hzero).toMeasure (sourcePairSuperpositionEvent G (fun m => P m ∧ CurrentConnected G m u v)) := by
-- proof
  apply StatMech.FrontierB.sourceCurrentPairPMF_switching G beta J hbeta hJ A huv P hAu huvSum hA hzero


-- created on 2026-10-23
