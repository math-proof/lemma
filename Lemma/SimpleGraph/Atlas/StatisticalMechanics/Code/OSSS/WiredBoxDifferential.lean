import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.OSSS.WiredBoxDifferential
open Finset Set StatMech StatMech.OSSS StatMech.OSSS.WiredBoxDifferential


/--
[boxActiveEdge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxDifferential.lean)
-/
@[path]
private lemma boxActiveEdge_injective_eq
  {d n : Nat} :
-- imply
  Function.Injective (boxActiveEdge d n) := by
-- proof
  apply StatMech.OSSS.WiredBoxDifferential.boxActiveEdge_injective d n

/--
[boxActiveEdge_eq_endpoints](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxDifferential.lean)
-/
@[path]
private lemma boxActiveEdge_eq_endpoints_eq
  {d n : Nat}
  {e : (boxGraph d n).edgeSet} :
-- imply
  boxActiveEdge d n e = s(boxActiveEndU d n e, boxActiveEndV d n e) := by
-- proof
  apply StatMech.OSSS.WiredBoxDifferential.boxActiveEdge_eq_endpoints d n e

/--
[boxActiveEnd_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxDifferential.lean)
-/
@[path]
private lemma boxActiveEnd_adj_eq
  {d n : Nat}
  {e : (boxGraph d n).edgeSet} :
-- imply
  (hypercubicLattice d).Adj (boxActiveEndU d n e) (boxActiveEndV d n e) := by
-- proof
  apply StatMech.OSSS.WiredBoxDifferential.boxActiveEnd_adj d n e

/--
[mem_osssBoxFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxDifferential.lean)
-/
@[path]
private lemma mem_osssBoxFinset_eq
  {d n : Nat}
  {x : Site d} :
-- imply
  x ∈ osssBoxFinset d n <-> x ∈ box d n := by
-- proof
  apply StatMech.OSSS.WiredBoxDifferential.mem_osssBoxFinset

/--
[mem_osssBoundaryFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxDifferential.lean)
-/
@[path]
private lemma mem_osssBoundaryFinset_eq
  {d n : Nat}
  {x : Site d} :
-- imply
  x ∈ osssBoundaryFinset d n <-> x ∈ vertexBoundary d n := by
-- proof
  apply StatMech.OSSS.WiredBoxDifferential.mem_osssBoundaryFinset

/--
[origin_mem_osssBoxFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxDifferential.lean)
-/
@[path]
private lemma origin_mem_osssBoxFinset_eq
  {d n : Nat} :
-- imply
  (0 : Site d) ∈ osssBoxFinset d n := by
-- proof
  apply StatMech.OSSS.WiredBoxDifferential.origin_mem_osssBoxFinset d n

/--
[origin_not_mem_osssBoundaryFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxDifferential.lean)
-/
@[path]
private lemma origin_not_mem_osssBoundaryFinset_eq
  {d k : Nat} :
-- imply
  (0 : Site d) ∉ osssBoundaryFinset d k := by
-- proof
  apply StatMech.OSSS.WiredBoxDifferential.origin_not_mem_osssBoundaryFinset d k

/--
[boxActiveEndU_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxDifferential.lean)
-/
@[path]
private lemma boxActiveEndU_mem_eq
  {d n : Nat}
  {e : (boxGraph d n).edgeSet} :
-- imply
  boxActiveEndU d n e ∈ osssBoxFinset d n := by
-- proof
  apply StatMech.OSSS.WiredBoxDifferential.boxActiveEndU_mem d n e

/--
[boxActiveEndV_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxDifferential.lean)
-/
@[path]
private lemma boxActiveEndV_mem_eq
  {d n : Nat}
  {e : (boxGraph d n).edgeSet} :
-- imply
  boxActiveEndV d n e ∈ osssBoxFinset d n := by
-- proof
  apply StatMech.OSSS.WiredBoxDifferential.boxActiveEndV_mem d n e

/--
[activeBox_crossProb_eq_wiredFull](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxDifferential.lean)
-/
@[path]
private lemma activeBox_crossProb_eq_wiredFull_eq
  {d n : Nat}
  {q beta : Real}
-- given
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  FK.activeBCProbOf (boxGraph d n) (wiredBoxBoundaryGraph d n) (FK.betaParams (fun _ => 1) beta) q (crossEvent (boxActiveEdge d n) 0 (vertexBoundary d n)) = wiredFullCrossMass d n q beta := by
-- proof
  apply StatMech.OSSS.WiredBoxDifferential.activeBox_crossProb_eq_wiredFull d n q beta hq hbeta

/--
[activeBox_cross_deriv_eq_wiredFull](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxDifferential.lean)
-/
@[path]
private lemma activeBox_cross_deriv_eq_wiredFull_eq
  {d n : Nat}
  {q beta : Real}
-- given
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  deriv (fun b => FK.activeBCProbOf (boxGraph d n) (wiredBoxBoundaryGraph d n) (FK.betaParams (fun _ => 1) b) q (crossEvent (boxActiveEdge d n) 0 (vertexBoundary d n))) beta = deriv (wiredFullCrossMass d n q) beta := by
-- proof
  apply StatMech.OSSS.WiredBoxDifferential.activeBox_cross_deriv_eq_wiredFull d n q beta hq hbeta

/--
[boxGraph_edgeSet_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxDifferential.lean)
-/
@[path]
private lemma boxGraph_edgeSet_nonempty_eq
  {d n : Nat}
-- given
  (hd : 1 <= d)
  (hn : 1 <= n) :
-- imply
  Nonempty (boxGraph d n).edgeSet := by
-- proof
  apply StatMech.OSSS.WiredBoxDifferential.boxGraph_edgeSet_nonempty d n hd hn

/--
[wired_box_differential_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxDifferential.lean)
-/
@[path]
private lemma wired_box_differential_inequality_eq
  {d n : Nat}
  {q beta beta0 : Real}
-- given
  (hd : 1 <= d)
  (hn : 1 <= n)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hbeta0 : beta <= beta0) :
-- imply
  exists c : Real, 0 < c ∧ c * (Lindeberg.mean (FK.activeBCProb (boxGraph d n) (wiredBoxBoundaryGraph d n) (FK.betaParams (fun _ => 1) beta) q) (crossIndG (boxActiveEdge d n) 0 n) / (4 * (osssBoxFinset d n).sup' (by exact ⟨0, origin_mem_osssBoxFinset d n⟩) (fun x => ∑ j ∈ Finset.range n, Lindeberg.mean (FK.activeBCProb (boxGraph d n) (wiredBoxBoundaryGraph d n) (FK.betaParams (fun _ => 1) beta) q) (fun omega => if ConnectedToSet d (liftCfg (boxActiveEdge d n) omega) x (centeredBoundary x j) then (1 : Real) else 0)) / (n : Real))) <= deriv (fun b => FK.activeBCProbOf (boxGraph d n) (wiredBoxBoundaryGraph d n) (FK.betaParams (fun _ => 1) b) q (crossEvent (boxActiveEdge d n) 0 (vertexBoundary d n))) beta := by
-- proof
  apply StatMech.OSSS.WiredBoxDifferential.wired_box_differential_inequality d n hd hn q beta beta0 hq hbeta hbeta0

/--
[wired_box_differential_inequality_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxDifferential.lean)
-/
@[path]
private lemma wired_box_differential_inequality_full_eq
  {d n : Nat}
  {q beta beta0 : Real}
-- given
  (hd : 1 <= d)
  (hn : 1 <= n)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hbeta0 : beta <= beta0) :
-- imply
  exists c : Real, 0 < c ∧ c * (wiredActiveTheta d n q beta / wiredActiveDenom d n q beta) <= deriv (wiredFullCrossMass d n q) beta := by
-- proof
  apply StatMech.OSSS.WiredBoxDifferential.wired_box_differential_inequality_full d n hd hn q beta beta0 hq hbeta hbeta0


-- created on 2026-10-23
