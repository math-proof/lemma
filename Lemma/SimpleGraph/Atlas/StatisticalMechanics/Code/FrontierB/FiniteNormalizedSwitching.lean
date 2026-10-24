import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierB.FiniteNormalizedSwitching
open StatMech StatMech.FrontierB


/--
[sourcePairNormalization_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteNormalizedSwitching.lean)
-/
@[path]
private lemma sourcePairNormalization_mul_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {A B : Finset V}
  [DecidablePred P]
-- given
  (P : Current V → Prop)
  (hA : 0 < currentSum G beta J A)
  (hB : 0 < currentSum G beta J B) :
-- imply
  (currentSum G beta J A * currentSum G beta J B) * normalizedGatedSourcePairSum G beta J A B P = gatedSourcePairSum G beta J A B P := by
-- proof
  apply StatMech.FrontierB.sourcePairNormalization_mul G beta J A B P hA hB

/--
[normalizedGatedSourcePairSum_switching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteNormalizedSwitching.lean)
-/
@[path]
private lemma normalizedGatedSourcePairSum_switching_eq
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
  (huv : u ≠ v)
  (P : Current V → Prop)
  (hAu : 0 < currentSum G beta J (A ∆ ({u, v} : Finset V)))
  (huvSum : 0 < currentSum G beta J ({u, v} : Finset V))
  (hA : 0 < currentSum G beta J A)
  (hzero : 0 < currentSum G beta J ∅) :
-- imply
  (currentSum G beta J (A ∆ ({u, v} : Finset V)) * currentSum G beta J ({u, v} : Finset V)) * normalizedGatedSourcePairSum G beta J (A ∆ ({u, v} : Finset V)) {u, v} P = (currentSum G beta J A * currentSum G beta J ∅) * normalizedGatedSourcePairSum G beta J A ∅ (fun m => P m ∧ CurrentConnected G m u v) := by
-- proof
  apply StatMech.FrontierB.normalizedGatedSourcePairSum_switching G beta J A huv P hAu huvSum hA hzero

/--
[normalizedGatedSourcePairSum_switching_local](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteNormalizedSwitching.lean)
-/
@[path]
private lemma normalizedGatedSourcePairSum_switching_local_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
  {u v : V}
  {S : Finset (Sym2 V)}
  [DecidablePred Q]
-- given
  (huv : u ≠ v)
  (Q : (↑S → ℕ) → Prop)
  (hAu : 0 < currentSum G beta J (A ∆ ({u, v} : Finset V)))
  (huvSum : 0 < currentSum G beta J ({u, v} : Finset V))
  (hA : 0 < currentSum G beta J A)
  (hzero : 0 < currentSum G beta J ∅) :
-- imply
  (currentSum G beta J (A ∆ ({u, v} : Finset V)) * currentSum G beta J ({u, v} : Finset V)) * normalizedGatedSourcePairSum G beta J (A ∆ ({u, v} : Finset V)) {u, v} (currentLocalPattern S Q) = (currentSum G beta J A * currentSum G beta J ∅) * normalizedGatedSourcePairSum G beta J A ∅ (fun m => currentLocalPattern S Q m ∧ CurrentConnected G m u v) := by
-- proof
  apply StatMech.FrontierB.normalizedGatedSourcePairSum_switching_local G beta J A huv S Q hAu huvSum hA hzero


-- created on 2026-10-23
