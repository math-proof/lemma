import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCoordinateReflectionGeometry.Part4
open StatMech StatMech.FrontierA


/--
[isingCoordinateReflect_apply_same](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionGeometry.lean)
-/
@[path]
private lemma isingCoordinateReflect_apply_same_eq
  {d : Nat}
  {i : Fin d}
  {m : Int}
  {x : Site d} :
-- imply
  isingCoordinateReflect i m x i = m - x i := by
-- proof
  apply StatMech.FrontierA.isingCoordinateReflect_apply_same i m x

/--
[isingCoordinateReflect_apply_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionGeometry.lean)
-/
@[path]
private lemma isingCoordinateReflect_apply_of_ne_eq
  {d : Nat}
  {i a : Fin d}
  {m : Int}
  {x : Site d}
-- given
  (hai : a ≠ i) :
-- imply
  isingCoordinateReflect i m x a = x a := by
-- proof
  apply StatMech.FrontierA.isingCoordinateReflect_apply_of_ne i a hai m x

/--
[isingCoordinateReflect_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionGeometry.lean)
-/
@[path]
private lemma isingCoordinateReflect_involutive_eq
  {d : Nat}
  {i : Fin d}
  {m : Int}
  {x : Site d} :
-- imply
  isingCoordinateReflect i m (isingCoordinateReflect i m x) = x := by
-- proof
  apply StatMech.FrontierA.isingCoordinateReflect_involutive i m x

/--
[hypercubicLattice_adj_coordinateReflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionGeometry.lean)
-/
@[path]
private lemma hypercubicLattice_adj_coordinateReflect_eq
  {d : Nat}
  {i : Fin d}
  {m : Int}
  {x y : Site d} :
-- imply
  (hypercubicLattice d).Adj x y ↔ (hypercubicLattice d).Adj (isingCoordinateReflect i m x) (isingCoordinateReflect i m y) := by
-- proof
  apply StatMech.FrontierA.hypercubicLattice_adj_coordinateReflect i m x y

/--
[isingCoordinateReflect_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionGeometry.lean)
-/
@[path]
private lemma isingCoordinateReflect_fixed_eq
  {d : Nat}
  {i : Fin d}
  {m : Int}
  {x : Site d}
-- given
  (hx : isingCoordinatePlane i m x) :
-- imply
  isingCoordinateReflect i m x = x := by
-- proof
  apply StatMech.FrontierA.isingCoordinateReflect_fixed i m x hx

/--
[isingCoordinateReflect_centered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionGeometry.lean)
-/
@[path]
private lemma isingCoordinateReflect_centered_eq
  {d : Nat}
  {i : Fin d}
  {m : Int}
  {x : Site d} :
-- imply
  2 * isingCoordinateReflect i m x i - m = -(2 * x i - m) := by
-- proof
  apply StatMech.FrontierA.isingCoordinateReflect_centered i m x

/--
[isingCoordinateReflect_lower_of_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionGeometry.lean)
-/
@[path]
private lemma isingCoordinateReflect_lower_of_upper_eq
  {d : Nat}
  {i : Fin d}
  {m : Int}
  {x : Site d}
-- given
  (hp : ¬ isingCoordinatePlane i m x)
  (hl : ¬ isingCoordinateLower i m x) :
-- imply
  isingCoordinateLower i m (isingCoordinateReflect i m x) := by
-- proof
  apply StatMech.FrontierA.isingCoordinateReflect_lower_of_upper i m x hp hl

/--
[isingCoordinateReflect_not_plane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionGeometry.lean)
-/
@[path]
private lemma isingCoordinateReflect_not_plane_eq
  {d : Nat}
  {i : Fin d}
  {m : Int}
  {x : Site d}
-- given
  (hp : ¬ isingCoordinatePlane i m x) :
-- imply
  ¬ isingCoordinatePlane i m (isingCoordinateReflect i m x) := by
-- proof
  apply StatMech.FrontierA.isingCoordinateReflect_not_plane i m x hp

/--
[isingCoordinateReflect_not_lower_of_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionGeometry.lean)
-/
@[path]
private lemma isingCoordinateReflect_not_lower_of_lower_eq
  {d : Nat}
  {i : Fin d}
  {m : Int}
  {x : Site d}
-- given
  (hl : isingCoordinateLower i m x) :
-- imply
  ¬ isingCoordinateLower i m (isingCoordinateReflect i m x) := by
-- proof
  apply StatMech.FrontierA.isingCoordinateReflect_not_lower_of_lower i m x hl

/--
[coordinateReflect_eq_of_adj_crossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionGeometry.lean)
-/
@[path]
private lemma coordinateReflect_eq_of_adj_crossing_eq
  {d : Nat}
  {i : Fin d}
  {m : Int}
  {x y : Site d}
-- given
  (hxy : (hypercubicLattice d).Adj x y)
  (hxl : isingCoordinateLower i m x)
  (hyp : ¬ isingCoordinatePlane i m y)
  (hyl : ¬ isingCoordinateLower i m y) :
-- imply
  isingCoordinateReflect i m x = y := by
-- proof
  apply StatMech.FrontierA.coordinateReflect_eq_of_adj_crossing i m hxy hxl hyp hyl

/--
[coordinateReflect_eq_of_adj_crossing_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionGeometry.lean)
-/
@[path]
private lemma coordinateReflect_eq_of_adj_crossing_symm_eq
  {d : Nat}
  {i : Fin d}
  {m : Int}
  {x y : Site d}
-- given
  (hxy : (hypercubicLattice d).Adj x y)
  (hyl : isingCoordinateLower i m y)
  (hxp : ¬ isingCoordinatePlane i m x)
  (hxl : ¬ isingCoordinateLower i m x) :
-- imply
  isingCoordinateReflect i m y = x := by
-- proof
  apply StatMech.FrontierA.coordinateReflect_eq_of_adj_crossing_symm i m hxy hyl hxp hxl

/--
[subset_isingCoordinateSymmetricHull](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionGeometry.lean)
-/
@[path]
private lemma subset_isingCoordinateSymmetricHull_eq
  {d : Nat}
  {K : Finset (Site d)}
  {i : Fin d}
  {m : Int} :
-- imply
  K ⊆ isingCoordinateSymmetricHull K i m := by
-- proof
  apply StatMech.FrontierA.subset_isingCoordinateSymmetricHull K i m

/--
[mem_isingCoordinateSymmetricHull_reflect_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionGeometry.lean)
-/
@[path]
private lemma mem_isingCoordinateSymmetricHull_reflect_iff_eq
  {d : Nat}
  {K : Finset (Site d)}
  {i : Fin d}
  {m : Int}
  {x : Site d} :
-- imply
  x ∈ isingCoordinateSymmetricHull K i m ↔ isingCoordinateReflect i m x ∈ isingCoordinateSymmetricHull K i m := by
-- proof
  apply StatMech.FrontierA.mem_isingCoordinateSymmetricHull_reflect_iff K i m x


-- created on 2026-10-23
