import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierB.PlusFreeSourceJointLimit
open Filter MeasureTheory StatMech StatMech.FrontierB


/--
[growingFreePairSourceCurrentMeasure_edge_inverse_tail_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusFreeSourceJointLimit.lean)
-/
@[path]
private lemma growingFreePairSourceCurrentMeasure_edge_inverse_tail_le_eq
  {d N : ℕ}
  {beta : ℝ}
  {x y : Site d}
  {k : ℕ}
  {e : Sym2 (Site d)}
  {K : ℕ}
-- given
  (hbeta : 0 < beta)
  (hx : x ∈ box d N)
  (hy : y ∈ box d N)
  (hxy : x ≠ y)
  (hK : 0 < K) :
-- imply
  (growingFreePairSourceCurrentMeasure d N beta hbeta x y hx hy hxy k : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) {m | K ≤ m e} ≤ ENNReal.ofReal (Real.exp beta / pairSourceBaseConstant d N beta x y hx hy) / K := by
-- proof
  apply StatMech.FrontierB.growingFreePairSourceCurrentMeasure_edge_inverse_tail_le d N beta hbeta x y hx hy hxy k e K hK

/--
[plusFreeSourceCurrentMeasure_joint_subsequence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusFreeSourceJointLimit.lean)
-/
@[path]
private lemma plusFreeSourceCurrentMeasure_joint_subsequence_eq
  {d N : ℕ}
  {beta : ℝ}
  {x y : Site d}
-- given
  (hbeta : 0 < beta)
  (hx : x ∈ box d N)
  (hy : y ∈ box d N)
  (hxy : x ≠ y) :
-- imply
  ∃ (nuFree nuPlus : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))) (phi : ℕ → ℕ), StrictMono phi ∧ WeakCurrentConverges ((growingFreePairSourceCurrentMeasure d N beta hbeta x y hx hy hxy) ∘ phi) nuFree ∧ WeakCurrentConverges ((growingPlusPairSourceCurrentMeasure d N beta hbeta x y hx hy hxy) ∘ phi) nuPlus := by
-- proof
  apply StatMech.FrontierB.plusFreeSourceCurrentMeasure_joint_subsequence d N beta hbeta x y hx hy hxy

/--
[plusFreeSourceCurrentSubsequence_strictMono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusFreeSourceJointLimit.lean)
-/
@[path]
private lemma plusFreeSourceCurrentSubsequence_strictMono_eq
  {d N : ℕ}
  {beta : ℝ}
  {x y : Site d}
-- given
  (hbeta : 0 < beta)
  (hx : x ∈ box d N)
  (hy : y ∈ box d N)
  (hxy : x ≠ y) :
-- imply
  StrictMono (plusFreeSourceCurrentSubsequence d N beta hbeta x y hx hy hxy) := by
-- proof
  apply StatMech.FrontierB.plusFreeSourceCurrentSubsequence_strictMono d N beta hbeta x y hx hy hxy

/--
[growingFreePairSourceCurrentMeasure_tendsto_jointLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusFreeSourceJointLimit.lean)
-/
@[path]
private lemma growingFreePairSourceCurrentMeasure_tendsto_jointLimit_eq
  {d N : ℕ}
  {beta : ℝ}
  {x y : Site d}
-- given
  (hbeta : 0 < beta)
  (hx : x ∈ box d N)
  (hy : y ∈ box d N)
  (hxy : x ≠ y) :
-- imply
  WeakCurrentConverges ((growingFreePairSourceCurrentMeasure d N beta hbeta x y hx hy hxy) ∘ plusFreeSourceCurrentSubsequence d N beta hbeta x y hx hy hxy) (infiniteFreePairSourceCurrentMeasure d N beta hbeta x y hx hy hxy) := by
-- proof
  apply StatMech.FrontierB.growingFreePairSourceCurrentMeasure_tendsto_jointLimit d N beta hbeta x y hx hy hxy

/--
[growingPlusPairSourceCurrentMeasure_tendsto_jointLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusFreeSourceJointLimit.lean)
-/
@[path]
private lemma growingPlusPairSourceCurrentMeasure_tendsto_jointLimit_eq
  {d N : ℕ}
  {beta : ℝ}
  {x y : Site d}
-- given
  (hbeta : 0 < beta)
  (hx : x ∈ box d N)
  (hy : y ∈ box d N)
  (hxy : x ≠ y) :
-- imply
  WeakCurrentConverges ((growingPlusPairSourceCurrentMeasure d N beta hbeta x y hx hy hxy) ∘ plusFreeSourceCurrentSubsequence d N beta hbeta x y hx hy hxy) (infinitePlusPairSourceCurrentMeasure d N beta hbeta x y hx hy hxy) := by
-- proof
  apply StatMech.FrontierB.growingPlusPairSourceCurrentMeasure_tendsto_jointLimit d N beta hbeta x y hx hy hxy

/--
[freeBoxCurrentMeasure_tendsto_along_plusFreeSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusFreeSourceJointLimit.lean)
-/
@[path]
private lemma freeBoxCurrentMeasure_tendsto_along_plusFreeSource_eq
  {d N : ℕ}
  {beta : ℝ}
  {x y : Site d}
-- given
  (hbeta : 0 < beta)
  (hx : x ∈ box d N)
  (hy : y ∈ box d N)
  (hxy : x ≠ y) :
-- imply
  WeakCurrentConverges (fun k => freeBoxCurrentMeasure d ((plusFreeSourceCurrentSubsequence d N beta hbeta x y hx hy hxy k + N) + 1) beta hbeta.le) (infiniteFreeCurrentMeasure d beta hbeta.le) := by
-- proof
  apply StatMech.FrontierB.freeBoxCurrentMeasure_tendsto_along_plusFreeSource d N beta hbeta x y hx hy hxy

/--
[plusBoxCurrentMeasure_tendsto_along_plusFreeSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusFreeSourceJointLimit.lean)
-/
@[path]
private lemma plusBoxCurrentMeasure_tendsto_along_plusFreeSource_eq
  {d N : ℕ}
  {beta : ℝ}
  {x y : Site d}
-- given
  (hbeta : 0 < beta)
  (hx : x ∈ box d N)
  (hy : y ∈ box d N)
  (hxy : x ≠ y) :
-- imply
  WeakCurrentConverges (fun k => plusBoxCurrentMeasure d ((plusFreeSourceCurrentSubsequence d N beta hbeta x y hx hy hxy k + N) + 1) beta hbeta.le) (infinitePlusCurrentMeasure d beta hbeta.le) := by
-- proof
  apply StatMech.FrontierB.plusBoxCurrentMeasure_tendsto_along_plusFreeSource d N beta hbeta x y hx hy hxy


-- created on 2026-10-23
