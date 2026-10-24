import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingFreeStateCoordinateSymmetry
open Filter MeasureTheory Set Topology StatMech StatMech.FrontierA


/--
[freeBoxAutomorphismEquiv_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingFreeStateCoordinateSymmetry.lean)
-/
@[path]
private lemma freeBoxAutomorphismEquiv_val_eq
  {d : Nat}
  {e : Site d ≃ Site d}
  {n : Nat}
  {x : freeDomainVertices (boxFinset d n)}
-- given
  (hbox : ∀ n x, x ∈ boxFinset d n ↔ e x ∈ boxFinset d n) :
-- imply
  (freeBoxAutomorphismEquiv e hbox n x).1 = e x.1 := by
-- proof
  apply StatMech.FrontierA.freeBoxAutomorphismEquiv_val e hbox n x

/--
[freeDomainSpinSupport_map_freeBoxAutomorphism](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingFreeStateCoordinateSymmetry.lean)
-/
@[path]
private lemma freeDomainSpinSupport_map_freeBoxAutomorphism_eq
  {d : Nat}
  {e : Site d ≃ Site d}
  {n : Nat}
  {A : Finset (Site d)}
-- given
  (hbox : ∀ n x, x ∈ boxFinset d n ↔ e x ∈ boxFinset d n) :
-- imply
  (freeDomainSpinSupport (boxFinset d n) A).map (freeBoxAutomorphismEquiv e hbox n).toEmbedding = freeDomainSpinSupport (boxFinset d n) (A.map e.toEmbedding) := by
-- proof
  apply StatMech.FrontierA.freeDomainSpinSupport_map_freeBoxAutomorphism e hbox n A

/--
[integral_freeState_spinProd_boxAutomorphism](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingFreeStateCoordinateSymmetry.lean)
-/
@[path]
private lemma integral_freeState_spinProd_boxAutomorphism_eq
  {d : Nat}
  {e : Site d ≃ Site d}
  {beta : Real}
  {A : Finset (Site d)}
-- given
  (hadj : ∀ x y, (hypercubicLattice d).Adj x y ↔ (hypercubicLattice d).Adj (e x) (e y))
  (hbox : ∀ n x, x ∈ boxFinset d n ↔ e x ∈ boxFinset d n)
  (hbeta : 0 <= beta) :
-- imply
  (∫ omega, spinProd (A.map e.toEmbedding) omega ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))) = ∫ omega, spinProd A omega ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.FrontierA.integral_freeState_spinProd_boxAutomorphism e hadj hbox beta hbeta A

/--
[isingCoordinateNegate_apply_same](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingFreeStateCoordinateSymmetry.lean)
-/
@[path]
private lemma isingCoordinateNegate_apply_same_eq
  {d : Nat}
  {i : Fin d}
  {x : Site d} :
-- imply
  isingCoordinateNegate i x i = -x i := by
-- proof
  apply StatMech.FrontierA.isingCoordinateNegate_apply_same i x

/--
[isingCoordinateNegate_apply_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingFreeStateCoordinateSymmetry.lean)
-/
@[path]
private lemma isingCoordinateNegate_apply_of_ne_eq
  {d : Nat}
  {i a : Fin d}
  {x : Site d}
-- given
  (hai : a ≠ i) :
-- imply
  isingCoordinateNegate i x a = x a := by
-- proof
  apply StatMech.FrontierA.isingCoordinateNegate_apply_of_ne i a hai x

/--
[isingCoordinateNegate_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingFreeStateCoordinateSymmetry.lean)
-/
@[path]
private lemma isingCoordinateNegate_involutive_eq
  {d : Nat}
  {i : Fin d}
  {x : Site d} :
-- imply
  isingCoordinateNegate i (isingCoordinateNegate i x) = x := by
-- proof
  apply StatMech.FrontierA.isingCoordinateNegate_involutive i x

/--
[hypercubicLattice_adj_coordinateNegate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingFreeStateCoordinateSymmetry.lean)
-/
@[path]
private lemma hypercubicLattice_adj_coordinateNegate_eq
  {d : Nat}
  {i : Fin d}
  {x y : Site d} :
-- imply
  (hypercubicLattice d).Adj x y ↔ (hypercubicLattice d).Adj (isingCoordinateNegate i x) (isingCoordinateNegate i y) := by
-- proof
  apply StatMech.FrontierA.hypercubicLattice_adj_coordinateNegate i x y

/--
[mem_boxFinset_coordinateNegate_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingFreeStateCoordinateSymmetry.lean)
-/
@[path]
private lemma mem_boxFinset_coordinateNegate_iff_eq
  {d : Nat}
  {i : Fin d}
  {n : Nat}
  {x : Site d} :
-- imply
  x ∈ boxFinset d n ↔ isingCoordinateNegate i x ∈ boxFinset d n := by
-- proof
  apply StatMech.FrontierA.mem_boxFinset_coordinateNegate_iff i n x

/--
[integral_freeState_spinProd_coordinateNegate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingFreeStateCoordinateSymmetry.lean)
-/
@[path]
private lemma integral_freeState_spinProd_coordinateNegate_eq
  {d : Nat}
  {i : Fin d}
  {beta : Real}
  {A : Finset (Site d)}
-- given
  (hbeta : 0 <= beta) :
-- imply
  (∫ omega, spinProd (A.map (isingCoordinateNegateEquiv i).toEmbedding) omega ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))) = ∫ omega, spinProd A omega ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.FrontierA.integral_freeState_spinProd_coordinateNegate i beta hbeta A

/--
[currentContinuityFreeTwoPoint_coordinateNegate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingFreeStateCoordinateSymmetry.lean)
-/
@[path]
private lemma currentContinuityFreeTwoPoint_coordinateNegate_eq
  {d : Nat}
  {i : Fin d}
  {beta : Real}
  {x : Site d}
-- given
  (hbeta : 0 <= beta) :
-- imply
  currentContinuityFreeTwoPoint d beta (Percolation.origin d) (isingCoordinateNegate i x) = currentContinuityFreeTwoPoint d beta (Percolation.origin d) x := by
-- proof
  apply StatMech.FrontierA.currentContinuityFreeTwoPoint_coordinateNegate i beta hbeta x

/--
[mem_boxFinset_diagonalReflect_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingFreeStateCoordinateSymmetry.lean)
-/
@[path]
private lemma mem_boxFinset_diagonalReflect_zero_iff_eq
  {d : Nat}
  {i j : Fin d}
  {n : Nat}
  {x : Site d}
-- given
  (hij : i ≠ j) :
-- imply
  x ∈ boxFinset d n ↔ isingDiagonalReflect i j 0 x ∈ boxFinset d n := by
-- proof
  apply StatMech.FrontierA.mem_boxFinset_diagonalReflect_zero_iff i j hij n x

/--
[currentContinuityFreeTwoPoint_coordinateSwap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingFreeStateCoordinateSymmetry.lean)
-/
@[path]
private lemma currentContinuityFreeTwoPoint_coordinateSwap_eq
  {d : Nat}
  {i j : Fin d}
  {beta : Real}
  {x : Site d}
-- given
  (hij : i ≠ j)
  (hbeta : 0 <= beta) :
-- imply
  currentContinuityFreeTwoPoint d beta (Percolation.origin d) (isingDiagonalReflect i j 0 x) = currentContinuityFreeTwoPoint d beta (Percolation.origin d) x := by
-- proof
  apply StatMech.FrontierA.currentContinuityFreeTwoPoint_coordinateSwap i j hij beta hbeta x


-- created on 2026-10-23
