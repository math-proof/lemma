import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.GHSUnconditional
open Set SimpleGraph StatMech StatMech.Sharpness


/--
[ghs_signDominance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GHSUnconditional.lean)
-/
@[path]
private lemma ghs_signDominance_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  GHSSignDominance G β h o := by
-- proof
  apply StatMech.Sharpness.ghs_signDominance G β h hβ hh o

/--
[ghs_magnetization_concaveOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GHSUnconditional.lean)
-/
@[path]
private lemma ghs_magnetization_concaveOn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {o : V}
-- given
  (hβ : 0 ≤ β) :
-- imply
  ConcaveOn ℝ (Ici 0) (fun h => isingExpectation G β h (fun s => spin s o)) := by
-- proof
  apply StatMech.Sharpness.ghs_magnetization_concaveOn G β hβ o

/--
[ghs_susceptibility_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GHSUnconditional.lean)
-/
@[path]
private lemma ghs_susceptibility_unconditional_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 < h) :
-- imply
  deriv (fun t => isingExpectation G β t (fun s => spin s o)) h = β * ∑ x, (isingExpectation G β h (fun s => spin s o * spin s x) - isingExpectation G β h (fun s => spin s o) * isingExpectation G β h (fun s => spin s x)) ∧ deriv (fun t => isingExpectation G β t (fun s => spin s o)) h ≤ 1 / h := by
-- proof
  apply StatMech.Sharpness.ghs_susceptibility_unconditional G β h hβ hh o


-- created on 2026-10-23
