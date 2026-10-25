import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionTouchingBondGeometry.Part4
open StatMech StatMech.FrontierA


/--
[sum_oddPrismTouchIndex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionTouchingBondGeometry.lean)
-/
@[path]
private lemma sum_oddPrismTouchIndex_eq
  {n : Nat}
-- given
  (f : OddPrismTouchIndex n -> Real) :
-- imply
  (∑ q, f q) = (∑ x, ∑ y, ∑ z, f (.xInternal x y z)) + (∑ x, ∑ y, ∑ z, f (.yInternal x y z)) + (∑ x, ∑ y, ∑ z, f (.zInternal x y z)) + (∑ y, ∑ z, f (.xZero y z)) + (∑ y, ∑ z, f (.xLast y z)) + (∑ x, ∑ z, f (.yZero x z)) + (∑ x, ∑ z, f (.yLast x z)) + (∑ x, ∑ y, f (.zZero x y)) + (∑ x, ∑ y, f (.zLast x y)) := by
-- proof
  apply StatMech.FrontierA.sum_oddPrismTouchIndex n f

/--
[oddPrismTouchIndexBond_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionTouchingBondGeometry.lean)
-/
@[path]
private lemma oddPrismTouchIndexBond_mem_eq
  {n : Nat}
  {q : OddPrismTouchIndex n} :
-- imply
  oddPrismTouchIndexBond n q ∈ bondFinsetTouch 3 n := by
-- proof
  apply StatMech.FrontierA.oddPrismTouchIndexBond_mem n q

/--
[touchingBondKey_xInternal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionTouchingBondGeometry.lean)
-/
@[path]
private lemma touchingBondKey_xInternal_eq
  {n : Nat}
  {x : Fin (2 * n)}
  {y z : Fin (2 * n + 1)} :
-- imply
  touchingBondKey (oddPrismTouchIndexBond n (.xInternal x y z)) = ((2 * (x.val : Int) + 1 - 2 * n, 2 * (y.val : Int) - 2 * n, 2 * (n : Int) - 2 * z.val), (1, 0, 0)) := by
-- proof
  apply StatMech.FrontierA.touchingBondKey_xInternal n x y z

/--
[touchingBondKey_yInternal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionTouchingBondGeometry.lean)
-/
@[path]
private lemma touchingBondKey_yInternal_eq
  {n : Nat}
  {x : Fin (2 * n + 1)}
  {y : Fin (2 * n)}
  {z : Fin (2 * n + 1)} :
-- imply
  touchingBondKey (oddPrismTouchIndexBond n (.yInternal x y z)) = ((2 * (x.val : Int) - 2 * n, 2 * (y.val : Int) + 1 - 2 * n, 2 * (n : Int) - 2 * z.val), (0, 1, 0)) := by
-- proof
  apply StatMech.FrontierA.touchingBondKey_yInternal n x y z

/--
[touchingBondKey_zInternal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionTouchingBondGeometry.lean)
-/
@[path]
private lemma touchingBondKey_zInternal_eq
  {n : Nat}
  {x y : Fin (2 * n + 1)}
  {z : Fin (2 * n)} :
-- imply
  touchingBondKey (oddPrismTouchIndexBond n (.zInternal x y z)) = ((2 * (x.val : Int) - 2 * n, 2 * (y.val : Int) - 2 * n, 2 * (n : Int) - 2 * z.val - 1), (0, 0, 1)) := by
-- proof
  apply StatMech.FrontierA.touchingBondKey_zInternal n x y z

/--
[touchingBondKey_xZero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionTouchingBondGeometry.lean)
-/
@[path]
private lemma touchingBondKey_xZero_eq
  {n : Nat}
  {y z : Fin (2 * n + 1)} :
-- imply
  touchingBondKey (oddPrismTouchIndexBond n (.xZero y z)) = ((-2 * (n : Int) - 1, 2 * (y.val : Int) - 2 * n, 2 * (n : Int) - 2 * z.val), (1, 0, 0)) := by
-- proof
  apply StatMech.FrontierA.touchingBondKey_xZero n y z

/--
[touchingBondKey_xLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionTouchingBondGeometry.lean)
-/
@[path]
private lemma touchingBondKey_xLast_eq
  {n : Nat}
  {y z : Fin (2 * n + 1)} :
-- imply
  touchingBondKey (oddPrismTouchIndexBond n (.xLast y z)) = ((2 * (n : Int) + 1, 2 * (y.val : Int) - 2 * n, 2 * (n : Int) - 2 * z.val), (1, 0, 0)) := by
-- proof
  apply StatMech.FrontierA.touchingBondKey_xLast n y z

/--
[touchingBondKey_yZero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionTouchingBondGeometry.lean)
-/
@[path]
private lemma touchingBondKey_yZero_eq
  {n : Nat}
  {x z : Fin (2 * n + 1)} :
-- imply
  touchingBondKey (oddPrismTouchIndexBond n (.yZero x z)) = ((2 * (x.val : Int) - 2 * n, -2 * (n : Int) - 1, 2 * (n : Int) - 2 * z.val), (0, 1, 0)) := by
-- proof
  apply StatMech.FrontierA.touchingBondKey_yZero n x z

/--
[touchingBondKey_yLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionTouchingBondGeometry.lean)
-/
@[path]
private lemma touchingBondKey_yLast_eq
  {n : Nat}
  {x z : Fin (2 * n + 1)} :
-- imply
  touchingBondKey (oddPrismTouchIndexBond n (.yLast x z)) = ((2 * (x.val : Int) - 2 * n, 2 * (n : Int) + 1, 2 * (n : Int) - 2 * z.val), (0, 1, 0)) := by
-- proof
  apply StatMech.FrontierA.touchingBondKey_yLast n x z

/--
[touchingBondKey_zZero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionTouchingBondGeometry.lean)
-/
@[path]
private lemma touchingBondKey_zZero_eq
  {n : Nat}
  {x y : Fin (2 * n + 1)} :
-- imply
  touchingBondKey (oddPrismTouchIndexBond n (.zZero x y)) = ((2 * (x.val : Int) - 2 * n, 2 * (y.val : Int) - 2 * n, 2 * (n : Int) + 1), (0, 0, 1)) := by
-- proof
  apply StatMech.FrontierA.touchingBondKey_zZero n x y

/--
[touchingBondKey_zLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionTouchingBondGeometry.lean)
-/
@[path]
private lemma touchingBondKey_zLast_eq
  {n : Nat}
  {x y : Fin (2 * n + 1)} :
-- imply
  touchingBondKey (oddPrismTouchIndexBond n (.zLast x y)) = ((2 * (x.val : Int) - 2 * n, 2 * (y.val : Int) - 2 * n, -2 * (n : Int) - 1), (0, 0, 1)) := by
-- proof
  apply StatMech.FrontierA.touchingBondKey_zLast n x y

/--
[oddPrismTouchIndexBond_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionTouchingBondGeometry.lean)
-/
@[path]
private lemma oddPrismTouchIndexBond_injective_eq
  {n : Nat} :
-- imply
  Function.Injective (oddPrismTouchIndexBond n) := by
-- proof
  apply StatMech.FrontierA.oddPrismTouchIndexBond_injective n

/--
[exists_oddPrism_xInternal_of_coordShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionTouchingBondGeometry.lean)
-/
@[path]
private lemma exists_oddPrism_xInternal_of_coordShift_eq
  {n : Nat}
  {a b : Site 3}
-- given
  (ha : a ∈ box 3 n)
  (hb : b ∈ box 3 n)
  (hab : b = coordShift a 0 1) :
-- imply
  ∃ q : OddPrismTouchIndex n, oddPrismTouchIndexBond n q = s(a, b) := by
-- proof
  apply StatMech.FrontierA.exists_oddPrism_xInternal_of_coordShift n ha hb hab

/--
[exists_oddPrism_yInternal_of_coordShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionTouchingBondGeometry.lean)
-/
@[path]
private lemma exists_oddPrism_yInternal_of_coordShift_eq
  {n : Nat}
  {a b : Site 3}
-- given
  (ha : a ∈ box 3 n)
  (hb : b ∈ box 3 n)
  (hab : b = coordShift a 1 1) :
-- imply
  ∃ q : OddPrismTouchIndex n, oddPrismTouchIndexBond n q = s(a, b) := by
-- proof
  apply StatMech.FrontierA.exists_oddPrism_yInternal_of_coordShift n ha hb hab

/--
[exists_oddPrism_zInternal_of_coordShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionTouchingBondGeometry.lean)
-/
@[path]
private lemma exists_oddPrism_zInternal_of_coordShift_eq
  {n : Nat}
  {a b : Site 3}
-- given
  (ha : a ∈ box 3 n)
  (hb : b ∈ box 3 n)
  (hab : b = coordShift a 2 1) :
-- imply
  ∃ q : OddPrismTouchIndex n, oddPrismTouchIndexBond n q = s(a, b) := by
-- proof
  apply StatMech.FrontierA.exists_oddPrism_zInternal_of_coordShift n ha hb hab

/--
[coordShift_neg_one_then_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionTouchingBondGeometry.lean)
-/
@[path]
private lemma coordShift_neg_one_then_one_eq
  {x : Site 3}
  {i : Fin 3} :
-- imply
  coordShift (coordShift x i (-1)) i 1 = x := by
-- proof
  apply StatMech.FrontierA.coordShift_neg_one_then_one x i

/--
[exists_oddPrism_internal_of_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionTouchingBondGeometry.lean)
-/
@[path]
private lemma exists_oddPrism_internal_of_adj_eq
  {n : Nat}
  {a b : Site 3}
-- given
  (ha : a ∈ box 3 n)
  (hb : b ∈ box 3 n)
  (hadj : (hypercubicLattice 3).Adj a b) :
-- imply
  ∃ q : OddPrismTouchIndex n, oddPrismTouchIndexBond n q = s(a, b) := by
-- proof
  apply StatMech.FrontierA.exists_oddPrism_internal_of_adj n ha hb hadj

/--
[exists_oddPrism_xZero_of_coordShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionTouchingBondGeometry.lean)
-/
@[path]
private lemma exists_oddPrism_xZero_of_coordShift_eq
  {n : Nat}
  {a b : Site 3}
-- given
  (ha : a ∈ box 3 n)
  (hb : b ∉ box 3 n)
  (hab : b = coordShift a 0 (-1)) :
-- imply
  ∃ q : OddPrismTouchIndex n, oddPrismTouchIndexBond n q = s(a, b) := by
-- proof
  apply StatMech.FrontierA.exists_oddPrism_xZero_of_coordShift n ha hb hab

/--
[exists_oddPrism_xLast_of_coordShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionTouchingBondGeometry.lean)
-/
@[path]
private lemma exists_oddPrism_xLast_of_coordShift_eq
  {n : Nat}
  {a b : Site 3}
-- given
  (ha : a ∈ box 3 n)
  (hb : b ∉ box 3 n)
  (hab : b = coordShift a 0 1) :
-- imply
  ∃ q : OddPrismTouchIndex n, oddPrismTouchIndexBond n q = s(a, b) := by
-- proof
  apply StatMech.FrontierA.exists_oddPrism_xLast_of_coordShift n ha hb hab

/--
[exists_oddPrism_yZero_of_coordShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionTouchingBondGeometry.lean)
-/
@[path]
private lemma exists_oddPrism_yZero_of_coordShift_eq
  {n : Nat}
  {a b : Site 3}
-- given
  (ha : a ∈ box 3 n)
  (hb : b ∉ box 3 n)
  (hab : b = coordShift a 1 (-1)) :
-- imply
  ∃ q : OddPrismTouchIndex n, oddPrismTouchIndexBond n q = s(a, b) := by
-- proof
  apply StatMech.FrontierA.exists_oddPrism_yZero_of_coordShift n ha hb hab

/--
[exists_oddPrism_yLast_of_coordShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionTouchingBondGeometry.lean)
-/
@[path]
private lemma exists_oddPrism_yLast_of_coordShift_eq
  {n : Nat}
  {a b : Site 3}
-- given
  (ha : a ∈ box 3 n)
  (hb : b ∉ box 3 n)
  (hab : b = coordShift a 1 1) :
-- imply
  ∃ q : OddPrismTouchIndex n, oddPrismTouchIndexBond n q = s(a, b) := by
-- proof
  apply StatMech.FrontierA.exists_oddPrism_yLast_of_coordShift n ha hb hab

/--
[exists_oddPrism_zZero_of_coordShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionTouchingBondGeometry.lean)
-/
@[path]
private lemma exists_oddPrism_zZero_of_coordShift_eq
  {n : Nat}
  {a b : Site 3}
-- given
  (ha : a ∈ box 3 n)
  (hb : b ∉ box 3 n)
  (hab : b = coordShift a 2 1) :
-- imply
  ∃ q : OddPrismTouchIndex n, oddPrismTouchIndexBond n q = s(a, b) := by
-- proof
  apply StatMech.FrontierA.exists_oddPrism_zZero_of_coordShift n ha hb hab

/--
[exists_oddPrism_zLast_of_coordShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionTouchingBondGeometry.lean)
-/
@[path]
private lemma exists_oddPrism_zLast_of_coordShift_eq
  {n : Nat}
  {a b : Site 3}
-- given
  (ha : a ∈ box 3 n)
  (hb : b ∉ box 3 n)
  (hab : b = coordShift a 2 (-1)) :
-- imply
  ∃ q : OddPrismTouchIndex n, oddPrismTouchIndexBond n q = s(a, b) := by
-- proof
  apply StatMech.FrontierA.exists_oddPrism_zLast_of_coordShift n ha hb hab

/--
[exists_oddPrism_boundary_of_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionTouchingBondGeometry.lean)
-/
@[path]
private lemma exists_oddPrism_boundary_of_adj_eq
  {n : Nat}
  {a b : Site 3}
-- given
  (ha : a ∈ box 3 n)
  (hb : b ∉ box 3 n)
  (hadj : (hypercubicLattice 3).Adj a b) :
-- imply
  ∃ q : OddPrismTouchIndex n, oddPrismTouchIndexBond n q = s(a, b) := by
-- proof
  apply StatMech.FrontierA.exists_oddPrism_boundary_of_adj n ha hb hadj

/--
[oddPrismTouchIndexBond_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionTouchingBondGeometry.lean)
-/
@[path]
private lemma oddPrismTouchIndexBond_surjective_eq
  {n : Nat} :
-- imply
  Function.Surjective (fun q : OddPrismTouchIndex n => (⟨oddPrismTouchIndexBond n q, oddPrismTouchIndexBond_mem n q⟩ : {e // e ∈ bondFinsetTouch 3 n})) := by
-- proof
  apply StatMech.FrontierA.oddPrismTouchIndexBond_surjective n

/--
[sum_bondFinsetTouch_eq_sum_oddPrismTouchIndex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionTouchingBondGeometry.lean)
-/
@[path]
private lemma sum_bondFinsetTouch_eq_sum_oddPrismTouchIndex_eq
  {n : Nat}
-- given
  (f : Sym2 (Site 3) -> Real) :
-- imply
  (∑ edge ∈ bondFinsetTouch 3 n, f edge) = ∑ q : OddPrismTouchIndex n, f (oddPrismTouchIndexBond n q) := by
-- proof
  apply StatMech.FrontierA.sum_bondFinsetTouch_eq_sum_oddPrismTouchIndex n f


-- created on 2026-10-23
