import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingFreeStateCoordinateMerge.Part4
open MeasureTheory StatMech StatMech.FrontierA


/--
[isingSignNormalize_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingFreeStateCoordinateMerge.lean)
-/
@[path]
private lemma isingSignNormalize_involutive_eq
  {d : Nat}
  {mask x : Site d} :
-- imply
  isingSignNormalize mask (isingSignNormalize mask x) = x := by
-- proof
  apply StatMech.FrontierA.isingSignNormalize_involutive mask x

/--
[hypercubicLattice_adj_signNormalize](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingFreeStateCoordinateMerge.lean)
-/
@[path]
private lemma hypercubicLattice_adj_signNormalize_eq
  {d : Nat}
  {mask x y : Site d} :
-- imply
  (hypercubicLattice d).Adj x y ↔ (hypercubicLattice d).Adj (isingSignNormalize mask x) (isingSignNormalize mask y) := by
-- proof
  apply StatMech.FrontierA.hypercubicLattice_adj_signNormalize mask x y

/--
[mem_boxFinset_signNormalize_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingFreeStateCoordinateMerge.lean)
-/
@[path]
private lemma mem_boxFinset_signNormalize_iff_eq
  {d : Nat}
  {mask : Site d}
  {n : Nat}
  {x : Site d} :
-- imply
  x ∈ boxFinset d n ↔ isingSignNormalize mask x ∈ boxFinset d n := by
-- proof
  apply StatMech.FrontierA.mem_boxFinset_signNormalize_iff mask n x

/--
[isingAbsSite_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingFreeStateCoordinateMerge.lean)
-/
@[path]
private lemma isingAbsSite_nonneg_eq
  {d : Nat}
  {x : Site d}
  {a : Fin d} :
-- imply
  0 <= isingAbsSite x a := by
-- proof
  apply StatMech.FrontierA.isingAbsSite_nonneg x a

/--
[isingSignNormalize_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingFreeStateCoordinateMerge.lean)
-/
@[path]
private lemma isingSignNormalize_self_eq
  {d : Nat}
  {x : Site d} :
-- imply
  isingSignNormalize x x = isingAbsSite x := by
-- proof
  apply StatMech.FrontierA.isingSignNormalize_self x

/--
[currentContinuityFreeTwoPoint_absSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingFreeStateCoordinateMerge.lean)
-/
@[path]
private lemma currentContinuityFreeTwoPoint_absSite_eq
  {d : Nat}
  {beta : Real}
  {x : Site d}
-- given
  (hbeta : 0 <= beta) :
-- imply
  currentContinuityFreeTwoPoint d beta (Percolation.origin d) (isingAbsSite x) = currentContinuityFreeTwoPoint d beta (Percolation.origin d) x := by
-- proof
  apply StatMech.FrontierA.currentContinuityFreeTwoPoint_absSite beta hbeta x

/--
[isingMergeFinset_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingFreeStateCoordinateMerge.lean)
-/
@[path]
private lemma isingMergeFinset_empty_eq
  {d : Nat}
  {i : Fin d}
  {x : Site d} :
-- imply
  isingMergeFinset i ∅ x = x := by
-- proof
  apply StatMech.FrontierA.isingMergeFinset_empty i x

/--
[isingMergeCoordinates_mergeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingFreeStateCoordinateMerge.lean)
-/
@[path]
private lemma isingMergeCoordinates_mergeFinset_eq
  {d : Nat}
  {i j : Fin d}
  {S : Finset (Fin d)}
  {x : Site d}
-- given
  (hij : i ≠ j)
  (hiS : i ∉ S)
  (hjS : j ∉ S) :
-- imply
  isingMergeCoordinates i j (isingMergeFinset i S x) = isingMergeFinset i (insert j S) x := by
-- proof
  apply StatMech.FrontierA.isingMergeCoordinates_mergeFinset i j S hij hiS hjS x

/--
[isingMergeFinset_accumulator_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingFreeStateCoordinateMerge.lean)
-/
@[path]
private lemma isingMergeFinset_accumulator_pos_eq
  {d : Nat}
  {i : Fin d}
  {S : Finset (Fin d)}
  {x : Site d}
-- given
  (hi : 0 < x i)
  (hS : ∀ j ∈ S, 0 <= x j) :
-- imply
  0 < isingMergeFinset i S x i := by
-- proof
  apply StatMech.FrontierA.isingMergeFinset_accumulator_pos i S x hi hS

/--
[currentContinuityFreeTwoPoint_mergeFinset_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingFreeStateCoordinateMerge.lean)
-/
@[path]
private lemma currentContinuityFreeTwoPoint_mergeFinset_le_eq
  {d : Nat}
  {i : Fin d}
  {S : Finset (Fin d)}
  {beta : Real}
  {x : Site d}
-- given
  (hiS : i ∉ S)
  (hbeta : 0 <= beta)
  (hi : 0 < x i)
  (hS : ∀ j ∈ S, 0 <= x j) :
-- imply
  currentContinuityFreeTwoPoint d beta (Percolation.origin d) (isingMergeFinset i S x) <= currentContinuityFreeTwoPoint d beta (Percolation.origin d) x := by
-- proof
  apply StatMech.FrontierA.currentContinuityFreeTwoPoint_mergeFinset_le i S hiS beta hbeta x hi hS

/--
[isingMergeFinset_erase_eq_single](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingFreeStateCoordinateMerge.lean)
-/
@[path]
private lemma isingMergeFinset_erase_eq_single_eq
  {d : Nat}
  {i : Fin d}
  {x : Site d} :
-- imply
  isingMergeFinset i (Finset.univ.erase i) x = Pi.single i (∑ j, x j) := by
-- proof
  apply StatMech.FrontierA.isingMergeFinset_erase_eq_single i x

/--
[currentContinuityFreeTwoPoint_axisSum_le_of_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingFreeStateCoordinateMerge.lean)
-/
@[path]
private lemma currentContinuityFreeTwoPoint_axisSum_le_of_nonneg_eq
  {d : Nat}
  {i : Fin d}
  {beta : Real}
  {x : Site d}
-- given
  (hbeta : 0 <= beta)
  (hi : 0 < x i)
  (hx : ∀ j, 0 <= x j) :
-- imply
  currentContinuityFreeTwoPoint d beta (Percolation.origin d) (Pi.single i (∑ j, x j)) <= currentContinuityFreeTwoPoint d beta (Percolation.origin d) x := by
-- proof
  apply StatMech.FrontierA.currentContinuityFreeTwoPoint_axisSum_le_of_nonneg i beta hbeta x hi hx

/--
[currentContinuityFreeTwoPoint_l1Axis_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingFreeStateCoordinateMerge.lean)
-/
@[path]
private lemma currentContinuityFreeTwoPoint_l1Axis_le_eq
  {d : Nat}
  {i : Fin d}
  {beta : Real}
  {x : Site d}
-- given
  (hbeta : 0 <= beta)
  (hi : x i ≠ 0) :
-- imply
  currentContinuityFreeTwoPoint d beta (Percolation.origin d) (Pi.single i ((∑ j, (x j).natAbs : Nat) : Int)) <= currentContinuityFreeTwoPoint d beta (Percolation.origin d) x := by
-- proof
  apply StatMech.FrontierA.currentContinuityFreeTwoPoint_l1Axis_le i beta hbeta x hi

/--
[currentContinuityFreeTwoPoint_axis_add_two_mul_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingFreeStateCoordinateMerge.lean)
-/
@[path]
private lemma currentContinuityFreeTwoPoint_axis_add_two_mul_le_eq
  {d : Nat}
  {i : Fin d}
  {beta : Real}
  {p : Nat}
  {t : Nat}
-- given
  (hd : 2 <= d)
  (hbeta : 0 <= beta)
  (hp : 0 < p) :
-- imply
  currentContinuityFreeTwoPoint d beta (Percolation.origin d) (Pi.single i (((p + 2 * t : Nat) : Int))) <= currentContinuityFreeTwoPoint d beta (Percolation.origin d) (Pi.single i (p : Int)) := by
-- proof
  apply StatMech.FrontierA.currentContinuityFreeTwoPoint_axis_add_two_mul_le hd i beta hbeta p hp t


-- created on 2026-10-23
