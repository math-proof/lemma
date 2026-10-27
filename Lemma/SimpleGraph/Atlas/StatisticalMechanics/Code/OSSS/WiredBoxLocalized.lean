import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.OSSS.WiredBoxLocalized.Part3
open StatMech StatMech.OSSS StatMech.OSSS.WiredBoxLocalized


/--
[boxActiveEdgeLE_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxLocalized.lean)
-/
@[path]
private lemma boxActiveEdgeLE_injective_eq
  {d : Nat}
  {n m : Nat}
-- given
  (h : n <= m) :
-- imply
  Function.Injective (boxActiveEdgeLE d h) := by
-- proof
  apply StatMech.OSSS.WiredBoxLocalized.boxActiveEdgeLE_injective d h

/--
[n_le_two_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxLocalized.lean)
-/
@[path]
private lemma n_le_two_mul_eq
  {n : Nat} :
-- imply
  n <= 2 * n := by
-- proof
  apply StatMech.OSSS.WiredBoxLocalized.n_le_two_mul n

/--
[innerCrossInd_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxLocalized.lean)
-/
@[path]
private lemma innerCrossInd_monotone_eq
  {d n : Nat} :
-- imply
  Monotone (innerCrossInd d n) := by
-- proof
  apply StatMech.OSSS.WiredBoxLocalized.innerCrossInd_monotone d n

/--
[innerCrossInd_idem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxLocalized.lean)
-/
@[path]
private lemma innerCrossInd_idem_eq
  {d n : Nat}
  {omega : ConfigSpace (boxGraph d (2 * n)).edgeSet} :
-- imply
  innerCrossInd d n omega * innerCrossInd d n omega = innerCrossInd d n omega := by
-- proof
  apply StatMech.OSSS.WiredBoxLocalized.innerCrossInd_idem d n omega

/--
[wiredOuterInnerConn_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxLocalized.lean)
-/
@[path]
private lemma wiredOuterInnerConn_nonneg_eq
  {d n : Nat}
  {q beta : Real}
  {x : Site d}
  {j : Nat}
-- given
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  0 <= wiredOuterInnerConn d n q beta x j := by
-- proof
  apply StatMech.OSSS.WiredBoxLocalized.wiredOuterInnerConn_nonneg d n q beta hq hbeta x j

/--
[wiredOuterInnerConn_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxLocalized.lean)
-/
@[path]
private lemma wiredOuterInnerConn_le_one_eq
  {d n : Nat}
  {q beta : Real}
  {x : Site d}
  {j : Nat}
-- given
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  wiredOuterInnerConn d n q beta x j <= 1 := by
-- proof
  apply StatMech.OSSS.WiredBoxLocalized.wiredOuterInnerConn_le_one d n q beta hq hbeta x j

/--
[wiredOuterInnerTheta_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxLocalized.lean)
-/
@[path]
private lemma wiredOuterInnerTheta_nonneg_eq
  {d : Nat}
  {q beta : Real}
  {k : Nat}
-- given
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  0 <= wiredOuterInnerTheta d q beta k := by
-- proof
  apply StatMech.OSSS.WiredBoxLocalized.wiredOuterInnerTheta_nonneg d q beta hq hbeta k

/--
[wiredOuterInnerConn_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxLocalized.lean)
-/
@[path]
private lemma wiredOuterInnerConn_antitone_eq
  {d n : Nat}
  {q beta : Real}
  {x : Site d}
-- given
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  Antitone (wiredOuterInnerConn d n q beta x) := by
-- proof
  apply StatMech.OSSS.WiredBoxLocalized.wiredOuterInnerConn_antitone d n q beta hq hbeta x

/--
[wiredOuterInnerConn_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxLocalized.lean)
-/
@[path]
private lemma wiredOuterInnerConn_zero_eq
  {d n : Nat}
  {q beta : Real}
  {x : Site d}
-- given
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  wiredOuterInnerConn d n q beta x 0 = 1 := by
-- proof
  apply StatMech.OSSS.WiredBoxLocalized.wiredOuterInnerConn_zero d n q beta hq hbeta x

/--
[wiredOuterInnerTheta_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxLocalized.lean)
-/
@[path]
private lemma wiredOuterInnerTheta_zero_eq
  {d : Nat}
  {q beta : Real}
-- given
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  wiredOuterInnerTheta d q beta 0 = 1 := by
-- proof
  apply StatMech.OSSS.WiredBoxLocalized.wiredOuterInnerTheta_zero d q beta hq hbeta

/--
[wiredOuterInner_sup_le_two_sig_of_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxLocalized.lean)
-/
@[path]
private lemma wiredOuterInner_sup_le_two_sig_of_comparison_eq
  {d n : Nat}
  {q beta : Real}
-- given
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hcomp : forall x, x ∈ osssBoxFinset d n -> forall k, k ∈ Finset.Icc 1 (n / 2) -> wiredOuterInnerConn d n q beta x k <= wiredOuterInnerTheta d q beta k) :
-- imply
  (osssBoxFinset d n).sup' ⟨0, origin_mem_osssBoxFinset d n⟩ (fun x => ∑ j ∈ Finset.range n, wiredOuterInnerConn d n q beta x j) <= 2 * wiredOuterInnerSig d n q beta := by
-- proof
  apply StatMech.OSSS.WiredBoxLocalized.wiredOuterInner_sup_le_two_sig_of_comparison d n q beta hq hbeta hcomp

/--
[wiredOuterInner_sup_le_two_sig_of_strict_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxLocalized.lean)
-/
@[path]
private lemma wiredOuterInner_sup_le_two_sig_of_strict_comparison_eq
  {d n : Nat}
  {q beta : Real}
-- given
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hcomp : forall x, x ∈ osssBoxFinset d n -> forall k, k ∈ Finset.Icc 1 (n / 2) -> 2 * k < n -> wiredOuterInnerConn d n q beta x k <= wiredOuterInnerTheta d q beta k) :
-- imply
  (osssBoxFinset d n).sup' ⟨0, origin_mem_osssBoxFinset d n⟩ (fun x => ∑ j ∈ Finset.range n, wiredOuterInnerConn d n q beta x j) <= 2 * wiredOuterInnerSig d n q beta := by
-- proof
  apply StatMech.OSSS.WiredBoxLocalized.wiredOuterInner_sup_le_two_sig_of_strict_comparison d n q beta hq hbeta hcomp

/--
[wiredOuterInnerDenom_le_eight_sig_of_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxLocalized.lean)
-/
@[path]
private lemma wiredOuterInnerDenom_le_eight_sig_of_comparison_eq
  {d n : Nat}
  {q beta : Real}
-- given
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hcomp : forall x, x ∈ osssBoxFinset d n -> forall k, k ∈ Finset.Icc 1 (n / 2) -> wiredOuterInnerConn d n q beta x k <= wiredOuterInnerTheta d q beta k) :
-- imply
  wiredOuterInnerDenom d n q beta <= 8 * wiredOuterInnerSig d n q beta / (n : Real) := by
-- proof
  apply StatMech.OSSS.WiredBoxLocalized.wiredOuterInnerDenom_le_eight_sig_of_comparison d n q beta hq hbeta hcomp

/--
[wiredOuterInnerDenom_le_eight_sig_of_strict_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxLocalized.lean)
-/
@[path]
private lemma wiredOuterInnerDenom_le_eight_sig_of_strict_comparison_eq
  {d n : Nat}
  {q beta : Real}
-- given
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hcomp : forall x, x ∈ osssBoxFinset d n -> forall k, k ∈ Finset.Icc 1 (n / 2) -> 2 * k < n -> wiredOuterInnerConn d n q beta x k <= wiredOuterInnerTheta d q beta k) :
-- imply
  wiredOuterInnerDenom d n q beta <= 8 * wiredOuterInnerSig d n q beta / (n : Real) := by
-- proof
  apply StatMech.OSSS.WiredBoxLocalized.wiredOuterInnerDenom_le_eight_sig_of_strict_comparison d n q beta hq hbeta hcomp

/--
[wiredOuterInnerDenom_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxLocalized.lean)
-/
@[path]
private lemma wiredOuterInnerDenom_pos_eq
  {d n : Nat}
  {q beta : Real}
-- given
  (hn : 1 <= n)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  0 < wiredOuterInnerDenom d n q beta := by
-- proof
  apply StatMech.OSSS.WiredBoxLocalized.wiredOuterInnerDenom_pos d n hn q beta hq hbeta

/--
[wiredOuterInnerSig_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxLocalized.lean)
-/
@[path]
private lemma wiredOuterInnerSig_pos_eq
  {d n : Nat}
  {q beta : Real}
-- given
  (hn : 1 <= n)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  0 < wiredOuterInnerSig d n q beta := by
-- proof
  apply StatMech.OSSS.WiredBoxLocalized.wiredOuterInnerSig_pos d n hn q beta hq hbeta

/--
[wired_outer_inner_hcov](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxLocalized.lean)
-/
@[path]
private lemma wired_outer_inner_hcov_eq
  {d n : Nat}
  {q beta D : Real}
-- given
  (hn : 1 <= n)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hD : 0 < D)
  (hsum : forall i : (boxGraph d n).edgeSet, (∑ k : ↑(Finset.Icc 1 n), localizedBoxReveal (FK.activeBCProb (boxGraph d (2 * n)) (wiredBoxBoundaryGraph d (2 * n)) (FK.betaParams (fun _ => 1) beta) q) (boxActiveEdgeLE d (n_le_two_mul n)) (boxActiveEdge d n) (boxActiveEndU d n) (boxActiveEndV d n) (k : Nat) i) <= (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D) :
-- imply
  Lindeberg.mean (FK.activeBCProb (boxGraph d (2 * n)) (wiredBoxBoundaryGraph d (2 * n)) (FK.betaParams (fun _ => 1) beta) q) (innerCrossInd d n) * (1 - Lindeberg.mean (FK.activeBCProb (boxGraph d (2 * n)) (wiredBoxBoundaryGraph d (2 * n)) (FK.betaParams (fun _ => 1) beta) q) (innerCrossInd d n)) / D <= ∑ e, Lindeberg.cov (FK.activeBCProb (boxGraph d (2 * n)) (wiredBoxBoundaryGraph d (2 * n)) (FK.betaParams (fun _ => 1) beta) q) (innerCrossInd d n) (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.WiredBoxLocalized.wired_outer_inner_hcov d n hn q beta D hq hbeta hD hsum

/--
[wired_outer_inner_hcov_geom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxLocalized.lean)
-/
@[path]
private lemma wired_outer_inner_hcov_geom_eq
  {d n : Nat}
  {q beta : Real}
-- given
  (hn : 1 <= n)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  Lindeberg.mean (FK.activeBCProb (boxGraph d (2 * n)) (wiredBoxBoundaryGraph d (2 * n)) (FK.betaParams (fun _ => 1) beta) q) (innerCrossInd d n) * (1 - Lindeberg.mean (FK.activeBCProb (boxGraph d (2 * n)) (wiredBoxBoundaryGraph d (2 * n)) (FK.betaParams (fun _ => 1) beta) q) (innerCrossInd d n)) / wiredOuterInnerDenom d n q beta <= ∑ e, Lindeberg.cov (FK.activeBCProb (boxGraph d (2 * n)) (wiredBoxBoundaryGraph d (2 * n)) (FK.betaParams (fun _ => 1) beta) q) (innerCrossInd d n) (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.WiredBoxLocalized.wired_outer_inner_hcov_geom d n hn q beta hq hbeta

/--
[wired_outer_inner_hcov_sharp_of_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxLocalized.lean)
-/
@[path]
private lemma wired_outer_inner_hcov_sharp_of_comparison_eq
  {d n : Nat}
  {q beta : Real}
-- given
  (hn : 1 <= n)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hcomp : forall x, x ∈ osssBoxFinset d n -> forall k, k ∈ Finset.Icc 1 (n / 2) -> wiredOuterInnerConn d n q beta x k <= wiredOuterInnerTheta d q beta k) :
-- imply
  Lindeberg.mean (FK.activeBCProb (boxGraph d (2 * n)) (wiredBoxBoundaryGraph d (2 * n)) (FK.betaParams (fun _ => 1) beta) q) (innerCrossInd d n) * (1 - Lindeberg.mean (FK.activeBCProb (boxGraph d (2 * n)) (wiredBoxBoundaryGraph d (2 * n)) (FK.betaParams (fun _ => 1) beta) q) (innerCrossInd d n)) / (8 * wiredOuterInnerSig d n q beta / (n : Real)) <= ∑ e, Lindeberg.cov (FK.activeBCProb (boxGraph d (2 * n)) (wiredBoxBoundaryGraph d (2 * n)) (FK.betaParams (fun _ => 1) beta) q) (innerCrossInd d n) (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.WiredBoxLocalized.wired_outer_inner_hcov_sharp_of_comparison d n hn q beta hq hbeta hcomp

/--
[wired_outer_inner_differential_logistic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxLocalized.lean)
-/
@[path]
private lemma wired_outer_inner_differential_logistic_eq
  {d n : Nat}
  {q beta D : Real}
-- given
  (hd : 1 <= d)
  (hn : 1 <= n)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hD : 0 < D)
  (hsum : forall i : (boxGraph d n).edgeSet, (∑ k : ↑(Finset.Icc 1 n), localizedBoxReveal (FK.activeBCProb (boxGraph d (2 * n)) (wiredBoxBoundaryGraph d (2 * n)) (FK.betaParams (fun _ => 1) beta) q) (boxActiveEdgeLE d (n_le_two_mul n)) (boxActiveEdge d n) (boxActiveEndU d n) (boxActiveEndV d n) (k : Nat) i) <= (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D) :
-- imply
  exists cR : Real, 0 < cR ∧ cR * (Lindeberg.mean (FK.activeBCProb (boxGraph d (2 * n)) (wiredBoxBoundaryGraph d (2 * n)) (FK.betaParams (fun _ => 1) beta) q) (innerCrossInd d n) * (1 - Lindeberg.mean (FK.activeBCProb (boxGraph d (2 * n)) (wiredBoxBoundaryGraph d (2 * n)) (FK.betaParams (fun _ => 1) beta) q) (innerCrossInd d n)) / D) <= deriv (fun b => FK.activeBCMean (boxGraph d (2 * n)) (wiredBoxBoundaryGraph d (2 * n)) (FK.betaParams (fun _ => 1) b) q (innerCrossInd d n)) beta := by
-- proof
  apply StatMech.OSSS.WiredBoxLocalized.wired_outer_inner_differential_logistic d n hd hn q beta D hq hbeta hD hsum


-- created on 2026-10-23
