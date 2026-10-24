import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.TriangularSharpness
open Finset Set Filter Topology MeasureTheory SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[triangularBox_end_coherent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpness.lean)
-/
@[path]
private lemma triangularBox_end_coherent_eq
  {n : Nat}
  {e : (triangularBoxGraph n).edgeSet} :
-- imply
  e.1 = s(triangularBoxEndU n e, triangularBoxEndV n e) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularBox_end_coherent n e

/--
[triangularBox_end_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpness.lean)
-/
@[path]
private lemma triangularBox_end_adj_eq
  {n : Nat}
  {e : (triangularBoxGraph n).edgeSet} :
-- imply
  (triangularBoxGraph n).Adj (triangularBoxEndU n e) (triangularBoxEndV n e) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularBox_end_adj n e

/--
[triangularBoxEdgeLE_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpness.lean)
-/
@[path]
private lemma triangularBoxEdgeLE_injective_eq
  {n m : Nat}
-- given
  (h : n ≤ m) :
-- imply
  Function.Injective (triangularBoxEdgeLE h) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularBoxEdgeLE_injective h

/--
[triangular_adj_mem_box_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpness.lean)
-/
@[path]
private lemma triangular_adj_mem_box_succ_eq
  {k : Nat}
  {x y : Site 2}
-- given
  (hx : x ∈ box 2 k)
  (hxy : triangularGraph.Adj x y) :
-- imply
  y ∈ box 2 (k + 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangular_adj_mem_box_succ hx hxy

/--
[triangular_adj_mem_box_of_mem_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpness.lean)
-/
@[path]
private lemma triangular_adj_mem_box_of_mem_pred_eq
  {k : Nat}
  {x y : Site 2}
-- given
  (hk : 1 ≤ k)
  (hx : x ∈ box 2 (k - 1))
  (hxy : triangularGraph.Adj x y) :
-- imply
  y ∈ box 2 k := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangular_adj_mem_box_of_mem_pred hk hx hxy

/--
[triangularBox_reachOpen_crosses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpness.lean)
-/
@[path]
private lemma triangularBox_reachOpen_crosses_eq
  {n k m : Nat}
  {omega : ConfigSpace (triangularBoxGraph n).edgeSet}
-- given
  (hk : 1 ≤ k)
  (hkm : k ≤ m)
  (h : ConnOpenSet (triangularBoxEndU n) (triangularBoxEndV n) omega (triangularBoxRoot n) (triangularBoxShell n m)) :
-- imply
  ConnOpenSet (triangularBoxEndU n) (triangularBoxEndV n) omega (triangularBoxRoot n) (triangularBoxShell n k) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularBox_reachOpen_crosses hk hkm omega h

/--
[triangularBoxGraph_edgeSet_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpness.lean)
-/
@[path]
private lemma triangularBoxGraph_edgeSet_nonempty_eq
  {n : Nat}
-- given
  (hn : 1 ≤ n) :
-- imply
  Nonempty (triangularBoxGraph n).edgeSet := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularBoxGraph_edgeSet_nonempty n hn

/--
[triangularInnerCrossInd_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpness.lean)
-/
@[path]
private lemma triangularInnerCrossInd_monotone_eq
  {n : Nat} :
-- imply
  Monotone (triangularInnerCrossInd n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularInnerCrossInd_monotone n

/--
[triangularInnerCrossInd_idem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpness.lean)
-/
@[path]
private lemma triangularInnerCrossInd_idem_eq
  {n : Nat}
  {omega : ConfigSpace (triangularBoxGraph (2 * n)).edgeSet} :
-- imply
  triangularInnerCrossInd n omega * triangularInnerCrossInd n omega = triangularInnerCrossInd n omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularInnerCrossInd_idem n omega

/--
[triangularOuterInnerDenom_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpness.lean)
-/
@[path]
private lemma triangularOuterInnerDenom_pos_eq
  {n : Nat}
  {q beta : Real}
-- given
  (hn : 1 ≤ n)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  0 < triangularOuterInnerDenom n q beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularOuterInnerDenom_pos n hn q beta hq hbeta

/--
[triangular_outer_inner_hcov](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpness.lean)
-/
@[path]
private lemma triangular_outer_inner_hcov_eq
  {n : Nat}
  {q beta D : Real}
-- given
  (hn : 1 ≤ n)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta)
  (hD : 0 < D)
  (hsum : ∀ e : (triangularBoxGraph n).edgeSet, (∑ k : ↑(Finset.Icc 1 n), (Lindeberg.mean (FK.activeBCProb (triangularBoxGraph (2 * n)) (triangularBoxBoundaryGraph (2 * n)) (FK.betaParams (fun _ => 1) beta) q) (fun omega => if ConnOpenSet (triangularBoxEndU n) (triangularBoxEndV n) (restrictConfig (triangularBoxEdgeLE (by omega : n ≤ 2 * n)) omega) (triangularBoxEndU n e) (triangularBoxShell n k) then (1 : Real) else 0) + Lindeberg.mean (FK.activeBCProb (triangularBoxGraph (2 * n)) (triangularBoxBoundaryGraph (2 * n)) (FK.betaParams (fun _ => 1) beta) q) (fun omega => if ConnOpenSet (triangularBoxEndU n) (triangularBoxEndV n) (restrictConfig (triangularBoxEdgeLE (by omega : n ≤ 2 * n)) omega) (triangularBoxEndV n e) (triangularBoxShell n k) then (1 : Real) else 0))) ≤ (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D) :
-- imply
  let mu := FK.activeBCProb (triangularBoxGraph (2 * n)) (triangularBoxBoundaryGraph (2 * n)) (FK.betaParams (fun _ => 1) beta) q Lindeberg.mean mu (triangularInnerCrossInd n) * (1 - Lindeberg.mean mu (triangularInnerCrossInd n)) / D ≤ ∑ e, Lindeberg.cov mu (triangularInnerCrossInd n) (Lindeberg.coord e) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangular_outer_inner_hcov n hn q beta D hq hbeta hD hsum

/--
[triangular_outer_inner_hcov_geom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpness.lean)
-/
@[path]
private lemma triangular_outer_inner_hcov_geom_eq
  {n : Nat}
  {q beta : Real}
-- given
  (hn : 1 ≤ n)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  let mu := FK.activeBCProb (triangularBoxGraph (2 * n)) (triangularBoxBoundaryGraph (2 * n)) (FK.betaParams (fun _ => 1) beta) q Lindeberg.mean mu (triangularInnerCrossInd n) * (1 - Lindeberg.mean mu (triangularInnerCrossInd n)) / triangularOuterInnerDenom n q beta ≤ ∑ e, Lindeberg.cov mu (triangularInnerCrossInd n) (Lindeberg.coord e) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangular_outer_inner_hcov_geom n hn q beta hq hbeta

/--
[triangular_outer_inner_differential_logistic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpness.lean)
-/
@[path]
private lemma triangular_outer_inner_differential_logistic_eq
  {n : Nat}
  {q beta : Real}
-- given
  (hn : 1 ≤ n)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  triangularOuterInnerTheta q beta n * (1 - triangularOuterInnerTheta q beta n) / triangularOuterInnerDenom n q beta ≤ triangularOuterInnerThetaPrime n q beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangular_outer_inner_differential_logistic n hn q beta hq hbeta

/--
[triangularBox_differential_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpness.lean)
-/
@[path]
private lemma triangularBox_differential_inequality_eq
  {n : Nat}
  {q beta beta0 : Real}
-- given
  (hn : 1 ≤ n)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta)
  (hbeta0 : beta ≤ beta0) :
-- imply
  ∃ c : Real, 0 < c ∧ c * (triangularBoxCrossMass n q beta / triangularBoxDenom n q beta) ≤ deriv (triangularBoxCrossMass n q) beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularBox_differential_inequality n hn q beta beta0 hq hbeta hbeta0


-- created on 2026-10-23
