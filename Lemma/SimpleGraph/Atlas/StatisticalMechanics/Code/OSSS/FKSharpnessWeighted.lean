import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeighted
open Finset Set StatMech StatMech.OSSS StatMech.OSSS.FKSharpnessWeighted


/--
[weighted_wired_box_hasDerivAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeighted.lean)
-/
@[path]
private lemma weighted_wired_box_hasDerivAt_eq
  {d n : ℕ}
  {J : Sym2 (boxVerts d n) → ℝ}
  {q beta : ℝ}
-- given
  (hJ : ∀ e, 0 < J e)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  HasDerivAt (fun b => FK.activeBCMean (boxGraph d n) (wiredBoxBoundaryGraph d n) (FK.betaParams J b) q (crossIndG (boxActiveEdge d n) 0 n)) (∑ e : (boxGraph d n).edgeSet, (J e.1 / (1 - Real.exp (-(beta * J e.1)))) * FK.activeBCCov (boxGraph d n) (wiredBoxBoundaryGraph d n) (FK.betaParams J beta) q (crossIndG (boxActiveEdge d n) 0 n) (Lindeberg.coord e)) beta := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeighted.weighted_wired_box_hasDerivAt d n J hJ q beta hq hbeta

/--
[weighted_wired_box_differential_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeighted.lean)
-/
@[path]
private lemma weighted_wired_box_differential_inequality_eq
  {d n : ℕ}
  {J : Sym2 (boxVerts d n) → ℝ}
  {q beta beta0 : ℝ}
-- given
  (hd : 1 ≤ d)
  (hn : 1 ≤ n)
  (hJ : ∀ e, 0 < J e)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta)
  (hbeta0 : beta ≤ beta0) :
-- imply
  ∃ c : ℝ, 0 < c ∧ c * (weightedWiredActiveTheta d n J q beta / weightedWiredActiveDenom d n J q beta) ≤ deriv (fun b => FK.activeBCProbOf (boxGraph d n) (wiredBoxBoundaryGraph d n) (FK.betaParams J b) q (crossEvent (boxActiveEdge d n) 0 (vertexBoundary d n))) beta := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeighted.weighted_wired_box_differential_inequality d n hd hn J hJ q beta beta0 hq hbeta hbeta0

/--
[weightedWiredActiveDenom_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeighted.lean)
-/
@[path]
private lemma weightedWiredActiveDenom_pos_eq
  {d n : ℕ}
  {J : Sym2 (boxVerts d n) → ℝ}
  {q beta : ℝ}
-- given
  (hn : 1 ≤ n)
  (hJ : ∀ e, 0 < J e)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  0 < weightedWiredActiveDenom d n J q beta := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeighted.weightedWiredActiveDenom_pos d n hn J hJ q beta hq hbeta


-- created on 2026-10-23
