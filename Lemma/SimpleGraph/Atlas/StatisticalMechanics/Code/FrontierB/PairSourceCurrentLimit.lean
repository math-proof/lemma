import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.PairSourceCurrentLimit.Part4
open Filter MeasureTheory StatMech StatMech.FrontierB


/--
[pairSourceBoxSite_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PairSourceCurrentLimit.lean)
-/
@[path]
private lemma pairSourceBoxSite_ne_eq
  {d n : ℕ}
  {x y : Site d}
-- given
  (hx : x ∈ box d n)
  (hy : y ∈ box d n)
  (hxy : x ≠ y) :
-- imply
  pairSourceBoxSite x hx ≠ pairSourceBoxSite y hy := by
-- proof
  apply StatMech.FrontierB.pairSourceBoxSite_ne hx hy hxy

/--
[boxSpinSupport_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PairSourceCurrentLimit.lean)
-/
@[path]
private lemma boxSpinSupport_pair_eq
  {d n : ℕ}
  {x y : Site d}
-- given
  (hx : x ∈ box d n)
  (hy : y ∈ box d n) :
-- imply
  boxSpinSupport d n {x, y} = {pairSourceBoxSite x hx, pairSourceBoxSite y hy} := by
-- proof
  apply StatMech.FrontierB.boxSpinSupport_pair hx hy

/--
[pairSourceBaseConstant_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PairSourceCurrentLimit.lean)
-/
@[path]
private lemma pairSourceBaseConstant_pos_eq
  {d N : ℕ}
  {beta : ℝ}
  {x y : Site d}
-- given
  (hbeta : 0 < beta)
  (hx : x ∈ box d N)
  (hy : y ∈ box d N) :
-- imply
  0 < pairSourceBaseConstant d N beta x y hx hy := by
-- proof
  apply StatMech.FrontierB.pairSourceBaseConstant_pos d N beta hbeta x y hx hy

/--
[pairSourceBaseConstant_le_expectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PairSourceCurrentLimit.lean)
-/
@[path]
private lemma pairSourceBaseConstant_le_expectation_eq
  {d N n : ℕ}
  {beta : ℝ}
  {x y : Site d}
-- given
  (hbeta : 0 < beta)
  (hx : x ∈ box d N)
  (hy : y ∈ box d N)
  (hxy : x ≠ y)
  (hNn : N ≤ n) :
-- imply
  pairSourceBaseConstant d N beta x y hx hy ≤ expectationJ (StatMech.FK.boxGraph d n) beta (fun _ => 1) {pairSourceBoxSite x (box_mono d hNn hx), pairSourceBoxSite y (box_mono d hNn hy)} := by
-- proof
  apply StatMech.FrontierB.pairSourceBaseConstant_le_expectation d N n beta hbeta x y hx hy hxy hNn

/--
[growingPairSourceCurrentMeasure_edge_inverse_tail_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PairSourceCurrentLimit.lean)
-/
@[path]
private lemma growingPairSourceCurrentMeasure_edge_inverse_tail_le_eq
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
  (growingPairSourceCurrentMeasure d N beta hbeta x y hx hy hxy k : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) {m | K ≤ m e} ≤ ENNReal.ofReal (Real.exp beta / pairSourceBaseConstant d N beta x y hx hy) / K := by
-- proof
  apply StatMech.FrontierB.growingPairSourceCurrentMeasure_edge_inverse_tail_le d N beta hbeta x y hx hy hxy k e K hK

/--
[growingPairSourceCurrentMeasure_subsequence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PairSourceCurrentLimit.lean)
-/
@[path]
private lemma growingPairSourceCurrentMeasure_subsequence_eq
  {d N : ℕ}
  {beta : ℝ}
  {x y : Site d}
-- given
  (hbeta : 0 < beta)
  (hx : x ∈ box d N)
  (hy : y ∈ box d N)
  (hxy : x ≠ y) :
-- imply
  ∃ (nu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))) (phi : ℕ → ℕ), StrictMono phi ∧ WeakCurrentConverges ((growingPairSourceCurrentMeasure d N beta hbeta x y hx hy hxy) ∘ phi) nu := by
-- proof
  apply StatMech.FrontierB.growingPairSourceCurrentMeasure_subsequence d N beta hbeta x y hx hy hxy

/--
[growingPairSourceCurrentMeasure_subsequence_with_cylinders](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PairSourceCurrentLimit.lean)
-/
@[path]
private lemma growingPairSourceCurrentMeasure_subsequence_with_cylinders_eq
  {d N : ℕ}
  {beta : ℝ}
  {x y : Site d}
-- given
  (hbeta : 0 < beta)
  (hx : x ∈ box d N)
  (hy : y ∈ box d N)
  (hxy : x ≠ y) :
-- imply
  ∃ (nu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))) (phi : ℕ → ℕ), StrictMono phi ∧ WeakCurrentConverges ((growingPairSourceCurrentMeasure d N beta hbeta x y hx hy hxy) ∘ phi) nu ∧ ∀ (S : Finset (Sym2 (Site d))) (A : Set (↑S → ℕ)), Tendsto (fun k => growingPairSourceCurrentMeasure d N beta hbeta x y hx hy hxy (phi k) (currentCylinder S A)) atTop (nhds (nu (currentCylinder S A))) := by
-- proof
  apply StatMech.FrontierB.growingPairSourceCurrentMeasure_subsequence_with_cylinders d N beta hbeta x y hx hy hxy

/--
[pairSourceCurrentBoxSubsequence_strictMono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PairSourceCurrentLimit.lean)
-/
@[path]
private lemma pairSourceCurrentBoxSubsequence_strictMono_eq
  {d N : ℕ}
  {beta : ℝ}
  {x y : Site d}
-- given
  (hbeta : 0 < beta)
  (hx : x ∈ box d N)
  (hy : y ∈ box d N)
  (hxy : x ≠ y) :
-- imply
  StrictMono (pairSourceCurrentBoxSubsequence d N beta hbeta x y hx hy hxy) := by
-- proof
  apply StatMech.FrontierB.pairSourceCurrentBoxSubsequence_strictMono d N beta hbeta x y hx hy hxy

/--
[growingPairSourceCurrentMeasure_tendsto_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PairSourceCurrentLimit.lean)
-/
@[path]
private lemma growingPairSourceCurrentMeasure_tendsto_infinite_eq
  {d N : ℕ}
  {beta : ℝ}
  {x y : Site d}
-- given
  (hbeta : 0 < beta)
  (hx : x ∈ box d N)
  (hy : y ∈ box d N)
  (hxy : x ≠ y) :
-- imply
  WeakCurrentConverges ((growingPairSourceCurrentMeasure d N beta hbeta x y hx hy hxy) ∘ pairSourceCurrentBoxSubsequence d N beta hbeta x y hx hy hxy) (infinitePairSourceCurrentMeasure d N beta hbeta x y hx hy hxy) := by
-- proof
  apply StatMech.FrontierB.growingPairSourceCurrentMeasure_tendsto_infinite d N beta hbeta x y hx hy hxy

/--
[freeBoxCurrentMeasure_tendsto_along_pairSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PairSourceCurrentLimit.lean)
-/
@[path]
private lemma freeBoxCurrentMeasure_tendsto_along_pairSource_eq
  {d N : ℕ}
  {beta : ℝ}
  {x y : Site d}
-- given
  (hbeta : 0 < beta)
  (hx : x ∈ box d N)
  (hy : y ∈ box d N)
  (hxy : x ≠ y) :
-- imply
  WeakCurrentConverges (fun k => freeBoxCurrentMeasure d (pairSourceCurrentBoxSubsequence d N beta hbeta x y hx hy hxy k + N) beta hbeta.le) (infiniteFreeCurrentMeasure d beta hbeta.le) := by
-- proof
  apply StatMech.FrontierB.freeBoxCurrentMeasure_tendsto_along_pairSource d N beta hbeta x y hx hy hxy

/--
[pairSourceBox_expectation_eq_freeIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PairSourceCurrentLimit.lean)
-/
@[path]
private lemma pairSourceBox_expectation_eq_freeIntegral_eq
  {d n : ℕ}
  {beta : ℝ}
  {x y : Site d}
-- given
  (hx : x ∈ box d n)
  (hy : y ∈ box d n) :
-- imply
  expectationJ (StatMech.FK.boxGraph d n) beta (fun _ => 1) {pairSourceBoxSite x hx, pairSourceBoxSite y hy} = ∫ omega, spinProd ({x, y} : Finset (Site d)) omega ∂(freeMeasure d n beta 0 : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.FrontierB.pairSourceBox_expectation_eq_freeIntegral d n beta x y hx hy

/--
[growingPairSource_expectation_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PairSourceCurrentLimit.lean)
-/
@[path]
private lemma growingPairSource_expectation_tendsto_eq
  {d N : ℕ}
  {beta : ℝ}
  {x y : Site d}
-- given
  (hbeta : 0 < beta)
  (hx : x ∈ box d N)
  (hy : y ∈ box d N) :
-- imply
  Tendsto (fun k => expectationJ (StatMech.FK.boxGraph d (k + N)) beta (fun _ => 1) {pairSourceBoxSite x (box_mono d (Nat.le_add_left N k) hx), pairSourceBoxSite y (box_mono d (Nat.le_add_left N k) hy)}) atTop (nhds (∫ omega, spinProd ({x, y} : Finset (Site d)) omega ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))))) := by
-- proof
  apply StatMech.FrontierB.growingPairSource_expectation_tendsto d N beta hbeta x y hx hy


-- created on 2026-10-23
