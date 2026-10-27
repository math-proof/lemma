import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.HexagonalSharpness.Part5
open Finset Set Filter Topology MeasureTheory SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[hexagonalBox_end_coherent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpness.lean)
-/
@[path]
private lemma hexagonalBox_end_coherent_eq
  {n : Nat}
  {e : (hexagonalBoxGraph n).edgeSet} :
-- imply
  e.1 = s(hexagonalBoxEndU n e, hexagonalBoxEndV n e) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalBox_end_coherent n e

/--
[hexagonalBox_end_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpness.lean)
-/
@[path]
private lemma hexagonalBox_end_adj_eq
  {n : Nat}
  {e : (hexagonalBoxGraph n).edgeSet} :
-- imply
  (hexagonalBoxGraph n).Adj (hexagonalBoxEndU n e) (hexagonalBoxEndV n e) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalBox_end_adj n e

/--
[hexagonalBoxEdgeLE_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpness.lean)
-/
@[path]
private lemma hexagonalBoxEdgeLE_injective_eq
  {n m : Nat}
-- given
  (h : n ≤ m) :
-- imply
  Function.Injective (hexagonalBoxEdgeLE h) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalBoxEdgeLE_injective h

/--
[hexagonal_adj_mem_box_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpness.lean)
-/
@[path]
private lemma hexagonal_adj_mem_box_succ_eq
  {k : Nat}
  {x y : HexVertex}
-- given
  (hx : x.1 ∈ box 2 k)
  (hxy : hexagonalGraph.Adj x y) :
-- imply
  y.1 ∈ box 2 (k + 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonal_adj_mem_box_succ hx hxy

/--
[hexagonal_adj_mem_box_of_mem_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpness.lean)
-/
@[path]
private lemma hexagonal_adj_mem_box_of_mem_pred_eq
  {k : Nat}
  {x y : HexVertex}
-- given
  (hk : 1 ≤ k)
  (hx : x.1 ∈ box 2 (k - 1))
  (hxy : hexagonalGraph.Adj x y) :
-- imply
  y.1 ∈ box 2 k := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonal_adj_mem_box_of_mem_pred hk hx hxy

/--
[hexagonalBox_reachOpen_crosses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpness.lean)
-/
@[path]
private lemma hexagonalBox_reachOpen_crosses_eq
  {n k m : Nat}
  {omega : ConfigSpace (hexagonalBoxGraph n).edgeSet}
-- given
  (hk : 1 ≤ k)
  (hkm : k ≤ m)
  (h : ConnOpenSet (hexagonalBoxEndU n) (hexagonalBoxEndV n) omega (hexagonalBoxRoot n) (hexagonalBoxShell n m)) :
-- imply
  ConnOpenSet (hexagonalBoxEndU n) (hexagonalBoxEndV n) omega (hexagonalBoxRoot n) (hexagonalBoxShell n k) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalBox_reachOpen_crosses hk hkm omega h

/--
[hexagonalBoxGraph_edgeSet_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpness.lean)
-/
@[path]
private lemma hexagonalBoxGraph_edgeSet_nonempty_eq
  {n : Nat}
-- given
  (hn : 1 ≤ n) :
-- imply
  Nonempty (hexagonalBoxGraph n).edgeSet := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalBoxGraph_edgeSet_nonempty n hn

/--
[hexagonalInnerCrossInd_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpness.lean)
-/
@[path]
private lemma hexagonalInnerCrossInd_monotone_eq
  {n : Nat} :
-- imply
  Monotone (hexagonalInnerCrossInd n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalInnerCrossInd_monotone n

/--
[hexagonalInnerCrossInd_idem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpness.lean)
-/
@[path]
private lemma hexagonalInnerCrossInd_idem_eq
  {n : Nat}
  {omega : ConfigSpace (hexagonalBoxGraph (2 * n)).edgeSet} :
-- imply
  hexagonalInnerCrossInd n omega * hexagonalInnerCrossInd n omega = hexagonalInnerCrossInd n omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalInnerCrossInd_idem n omega

/--
[hexagonalOuterInnerDenom_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpness.lean)
-/
@[path]
private lemma hexagonalOuterInnerDenom_pos_eq
  {n : Nat}
  {q beta : Real}
-- given
  (hn : 1 ≤ n)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  0 < hexagonalOuterInnerDenom n q beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalOuterInnerDenom_pos n hn q beta hq hbeta

/--
[hexagonal_outer_inner_hcov](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpness.lean)
-/
@[path]
private lemma hexagonal_outer_inner_hcov_eq
  {n : Nat}
  {q beta D : Real}
-- given
  (hn : 1 ≤ n)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta)
  (hD : 0 < D)
  (hsum : ∀ e : (hexagonalBoxGraph n).edgeSet, (∑ k : ↑(Finset.Icc 1 n), (Lindeberg.mean (FK.activeBCProb (hexagonalBoxGraph (2 * n)) (hexagonalBoxBoundaryGraph (2 * n)) (FK.betaParams (fun _ => 1) beta) q) (fun omega => if ConnOpenSet (hexagonalBoxEndU n) (hexagonalBoxEndV n) (restrictConfig (hexagonalBoxEdgeLE (by omega : n ≤ 2 * n)) omega) (hexagonalBoxEndU n e) (hexagonalBoxShell n k) then (1 : Real) else 0) + Lindeberg.mean (FK.activeBCProb (hexagonalBoxGraph (2 * n)) (hexagonalBoxBoundaryGraph (2 * n)) (FK.betaParams (fun _ => 1) beta) q) (fun omega => if ConnOpenSet (hexagonalBoxEndU n) (hexagonalBoxEndV n) (restrictConfig (hexagonalBoxEdgeLE (by omega : n ≤ 2 * n)) omega) (hexagonalBoxEndV n e) (hexagonalBoxShell n k) then (1 : Real) else 0))) ≤ (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D) :
-- imply
  let mu := FK.activeBCProb (hexagonalBoxGraph (2 * n)) (hexagonalBoxBoundaryGraph (2 * n)) (FK.betaParams (fun _ => 1) beta) q Lindeberg.mean mu (hexagonalInnerCrossInd n) * (1 - Lindeberg.mean mu (hexagonalInnerCrossInd n)) / D ≤ ∑ e, Lindeberg.cov mu (hexagonalInnerCrossInd n) (Lindeberg.coord e) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonal_outer_inner_hcov n hn q beta D hq hbeta hD hsum

/--
[hexagonal_outer_inner_hcov_geom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpness.lean)
-/
@[path]
private lemma hexagonal_outer_inner_hcov_geom_eq
  {n : Nat}
  {q beta : Real}
-- given
  (hn : 1 ≤ n)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  let mu := FK.activeBCProb (hexagonalBoxGraph (2 * n)) (hexagonalBoxBoundaryGraph (2 * n)) (FK.betaParams (fun _ => 1) beta) q Lindeberg.mean mu (hexagonalInnerCrossInd n) * (1 - Lindeberg.mean mu (hexagonalInnerCrossInd n)) / hexagonalOuterInnerDenom n q beta ≤ ∑ e, Lindeberg.cov mu (hexagonalInnerCrossInd n) (Lindeberg.coord e) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonal_outer_inner_hcov_geom n hn q beta hq hbeta

/--
[hexagonal_outer_inner_differential_logistic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpness.lean)
-/
@[path]
private lemma hexagonal_outer_inner_differential_logistic_eq
  {n : Nat}
  {q beta : Real}
-- given
  (hn : 1 ≤ n)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  hexagonalOuterInnerTheta q beta n * (1 - hexagonalOuterInnerTheta q beta n) / hexagonalOuterInnerDenom n q beta ≤ hexagonalOuterInnerThetaPrime n q beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonal_outer_inner_differential_logistic n hn q beta hq hbeta

/--
[hexagonalBox_differential_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpness.lean)
-/
@[path]
private lemma hexagonalBox_differential_inequality_eq
  {n : Nat}
  {q beta beta0 : Real}
-- given
  (hn : 1 ≤ n)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta)
  (hbeta0 : beta ≤ beta0) :
-- imply
  ∃ c : Real, 0 < c ∧ c * (hexagonalBoxCrossMass n q beta / hexagonalBoxDenom n q beta) ≤ deriv (hexagonalBoxCrossMass n q) beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalBox_differential_inequality n hn q beta beta0 hq hbeta hbeta0


-- created on 2026-10-23
