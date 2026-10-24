import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierB.BoundaryCurrentTail
open MeasureTheory StatMech StatMech.FrontierB


/--
[extendInteriorPlus_inside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundaryCurrentTail.lean)
-/
@[path]
private lemma extendInteriorPlus_inside_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {interior : Finset V}
  {s : ConfigSpace ↑interior}
  {v : ↑interior} :
-- imply
  extendInteriorPlus interior s v.1 = s v := by
-- proof
  apply StatMech.FrontierB.extendInteriorPlus_inside G interior s v

/--
[extendInteriorPlus_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundaryCurrentTail.lean)
-/
@[path]
private lemma extendInteriorPlus_outside_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {interior : Finset V}
  {s : ConfigSpace ↑interior}
  {v : V}
-- given
  (hv : v ∉ interior) :
-- imply
  extendInteriorPlus interior s v = true := by
-- proof
  apply StatMech.FrontierB.extendInteriorPlus_outside G interior s v hv

/--
[prod_spin_extendInteriorPlus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundaryCurrentTail.lean)
-/
@[path]
private lemma prod_spin_extendInteriorPlus_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {interior : Finset V}
  {s : ConfigSpace ↑interior}
  {a : V → ℕ} :
-- imply
  (∏ v : V, spin (extendInteriorPlus interior s) v ^ a v) = ∏ v : ↑interior, spin s v ^ a v.1 := by
-- proof
  apply StatMech.FrontierB.prod_spin_extendInteriorPlus G interior s a

/--
[interiorSpinSum_monomial_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundaryCurrentTail.lean)
-/
@[path]
private lemma interiorSpinSum_monomial_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {interior : Finset V}
  {n : Sharpness.Current V} :
-- imply
  (∑ s : ConfigSpace ↑interior, ∏ e ∈ G.edgeFinset, bond (extendInteriorPlus interior s) e ^ n e) = if (sources G n) ∩ interior = ∅ then (2 : ℝ) ^ interior.card else 0 := by
-- proof
  apply StatMech.FrontierB.interiorSpinSum_monomial_eq G interior n

/--
[boundaryPartitionJ_eq_boundaryCurrentSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundaryCurrentTail.lean)
-/
@[path]
private lemma boundaryPartitionJ_eq_boundaryCurrentSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {interior : Finset V} :
-- imply
  boundaryPartitionJ G beta J interior = (2 : ℝ) ^ interior.card * boundaryCurrentSum G beta J interior := by
-- proof
  apply StatMech.FrontierB.boundaryPartitionJ_eq_boundaryCurrentSum G beta J interior

/--
[boundaryPartitionJ_doubledEdgeCoupling_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundaryCurrentTail.lean)
-/
@[path]
private lemma boundaryPartitionJ_doubledEdgeCoupling_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {interior : Finset V}
  {e : G.edgeFinset}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ f, 0 ≤ J f) :
-- imply
  boundaryPartitionJ G beta (doubledEdgeCoupling J e.1) interior ≤ Real.exp (beta * J e.1) * boundaryPartitionJ G beta J interior := by
-- proof
  apply StatMech.FrontierB.boundaryPartitionJ_doubledEdgeCoupling_le G beta J hbeta hJ interior e

/--
[boundaryCurrentSum_doubledEdgeCoupling_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundaryCurrentTail.lean)
-/
@[path]
private lemma boundaryCurrentSum_doubledEdgeCoupling_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {interior : Finset V}
  {e : G.edgeFinset}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ f, 0 ≤ J f) :
-- imply
  boundaryCurrentSum G beta (doubledEdgeCoupling J e.1) interior ≤ Real.exp (beta * J e.1) * boundaryCurrentSum G beta J interior := by
-- proof
  apply StatMech.FrontierB.boundaryCurrentSum_doubledEdgeCoupling_le G beta J hbeta hJ interior e

/--
[boundary_current_tail_doubling_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundaryCurrentTail.lean)
-/
@[path]
private lemma boundary_current_tail_doubling_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {interior : Finset V}
  {e : G.edgeFinset}
  {K : ℕ}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ f, 0 ≤ J f) :
-- imply
  (∑' m : EdgeCurrent G, if (sources G (ofEdgeFun G m)) ∩ interior = ∅ ∧ K ≤ m e then weight G beta J (ofEdgeFun G m) else 0) ≤ ((2 : ℝ) ^ K)⁻¹ * boundaryCurrentSum G beta (doubledEdgeCoupling J e.1) interior := by
-- proof
  apply StatMech.FrontierB.boundary_current_tail_doubling_le G beta J hbeta hJ interior e K

/--
[boundaryCurrentMeasure_edge_exponential_tail_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundaryCurrentTail.lean)
-/
@[path]
private lemma boundaryCurrentMeasure_edge_exponential_tail_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {interior : Finset V}
  {e : G.edgeFinset}
  {K : ℕ}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ f, 0 ≤ J f) :
-- imply
  (boundaryCurrentMeasure G beta J hbeta hJ interior : Measure (EdgeCurrent G)) {m | K ≤ m e} ≤ ENNReal.ofReal (Real.exp (beta * J e.1) / (2 : ℝ) ^ K) := by
-- proof
  apply StatMech.FrontierB.boundaryCurrentMeasure_edge_exponential_tail_le G beta J hbeta hJ interior e K

/--
[boundaryCurrentMeasure_edge_inverse_tail_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoundaryCurrentTail.lean)
-/
@[path]
private lemma boundaryCurrentMeasure_edge_inverse_tail_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {interior : Finset V}
  {e : G.edgeFinset}
  {K : ℕ}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ f, 0 ≤ J f)
  (hK : 0 < K) :
-- imply
  (boundaryCurrentMeasure G beta J hbeta hJ interior : Measure (EdgeCurrent G)) {m | K ≤ m e} ≤ ENNReal.ofReal (Real.exp (beta * J e.1) / K) := by
-- proof
  apply StatMech.FrontierB.boundaryCurrentMeasure_edge_inverse_tail_le G beta J hbeta hJ interior e K hK


-- created on 2026-10-23
