import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceScheduledCapstone
open Filter Topology StatMech StatMech.FrontierD


/--
[fkQgt4_fixedCharge_bound_of_uniformDiagonalWinding_boundaryIncidenceTail_fourCopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceScheduledCapstone.lean)
-/
@[path]
private lemma fkQgt4_fixedCharge_bound_of_uniformDiagonalWinding_boundaryIncidenceTail_fourCopy_eq
  {q xiInv : Real}
  {r : Nat}
  {crossingThreshold : (Nat → Nat) → Nat → Nat}
-- given
  (hq : 4 < q)
  (hr : 2 ≤ r)
  (heightLower : Nat → Nat)
  (hwind : ∀ m : Nat → Nat, (∀ k, heightLower k ≤ m k) → Tendsto (fun k => -Real.log (fkRectCriticalWindingTailMass (fkRectFixedChargeVerticalFamily r k (m k)) q r) / (fkRectFixedChargeVerticalFamily r k (m k)).height) atTop (nhds (((r - 1 : Nat) : Real) * xiInv)))
  (hsmall : ∀ m : Nat → Nat, (∀ k, heightLower k ≤ m k) → ∀ k, let R := fkRectFixedChargeVerticalFamily r k (m k) let n := crossingThreshold m k Nat.choose R.height (n + 1) * ((FK.freeInfiniteVolume 2 (fkRectCriticalP_pos (by linarith : 0 < q)) (fkRectCriticalP_lt_one (by linarith : 0 < q)) (by linarith : 0 < q) : MeasureTheory.Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))).real (FK.boxBdryConnEvent 2 (R.width - 2))) ^ (n + 1) ≤ FK.cFE (fkRectCriticalP q) q ^ (2 * R.width + R.height) / 2)
  (hwidth : ∀ m : Nat → Nat, (∀ k, heightLower k ≤ m k) → Tendsto (fun k => ((fkRectFixedChargeVerticalFamily r k (m k)).width : Real) / (fkRectFixedChargeVerticalFamily r k (m k)).height) atTop (nhds 0))
  (hthreshold : ∀ m : Nat → Nat, (∀ k, heightLower k ≤ m k) → Tendsto (fun k => (crossingThreshold m k : Real) / (fkRectFixedChargeVerticalFamily r k (m k)).height) atTop (nhds 0))
  (hheight : ∀ m : Nat → Nat, (∀ k, heightLower k ≤ m k) → Tendsto (fun k => (fkRectFixedChargeVerticalFamily r k (m k)).height) atTop atTop)
  (hfourCopy : ∀ m : Nat → Nat, (∀ k, heightLower k ≤ m k) → Tendsto (fun k => fkRectFourCopyShareCost (fkRectFixedChargeVerticalFamily r k (m k)) q / (fkRectFixedChargeVerticalFamily r k (m k)).height) atTop (nhds 0)) :
-- imply
  ((r - 1 : Nat) : Real) * xiInv ≤ (r : Real) * fkQgt4SixVertexGapRate q := by
-- proof
  apply StatMech.FrontierD.fkQgt4_fixedCharge_bound_of_uniformDiagonalWinding_boundaryIncidenceTail_fourCopy hq r hr heightLower crossingThreshold hwind hsmall hwidth hthreshold hheight hfourCopy


-- created on 2026-10-23
