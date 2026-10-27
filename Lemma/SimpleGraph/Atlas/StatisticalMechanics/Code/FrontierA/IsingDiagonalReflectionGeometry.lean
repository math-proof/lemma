import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingDiagonalReflectionGeometry.Part2
open StatMech StatMech.FrontierA


/--
[isingDiagonalReflect_apply_i](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDiagonalReflectionGeometry.lean)
-/
@[path]
private lemma isingDiagonalReflect_apply_i_eq
  {d : Nat}
  {i j : Fin d}
  {c : Int}
  {x : Site d}
-- given
  (hij : i ≠ j) :
-- imply
  isingDiagonalReflect i j c x i = x j + c := by
-- proof
  apply StatMech.FrontierA.isingDiagonalReflect_apply_i i j hij c x

/--
[isingDiagonalReflect_apply_j](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDiagonalReflectionGeometry.lean)
-/
@[path]
private lemma isingDiagonalReflect_apply_j_eq
  {d : Nat}
  {i j : Fin d}
  {c : Int}
  {x : Site d}
-- given
  (hij : i ≠ j) :
-- imply
  isingDiagonalReflect i j c x j = x i - c := by
-- proof
  apply StatMech.FrontierA.isingDiagonalReflect_apply_j i j hij c x

/--
[isingDiagonalReflect_apply_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDiagonalReflectionGeometry.lean)
-/
@[path]
private lemma isingDiagonalReflect_apply_of_ne_eq
  {d : Nat}
  {i j a : Fin d}
  {c : Int}
  {x : Site d}
-- given
  (hai : a ≠ i)
  (haj : a ≠ j) :
-- imply
  isingDiagonalReflect i j c x a = x a := by
-- proof
  apply StatMech.FrontierA.isingDiagonalReflect_apply_of_ne i j a hai haj c x

/--
[isingDiagonalReflect_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDiagonalReflectionGeometry.lean)
-/
@[path]
private lemma isingDiagonalReflect_involutive_eq
  {d : Nat}
  {i j : Fin d}
  {c : Int}
  {x : Site d}
-- given
  (hij : i ≠ j) :
-- imply
  isingDiagonalReflect i j c (isingDiagonalReflect i j c x) = x := by
-- proof
  apply StatMech.FrontierA.isingDiagonalReflect_involutive i j hij c x

/--
[isingDiagonalReflect_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDiagonalReflectionGeometry.lean)
-/
@[path]
private lemma isingDiagonalReflect_sub_eq
  {d : Nat}
  {i j : Fin d}
  {c : Int}
  {x y : Site d}
  {a : Fin d} :
-- imply
  isingDiagonalReflect i j c x a - isingDiagonalReflect i j c y a = x (Equiv.swap i j a) - y (Equiv.swap i j a) := by
-- proof
  apply StatMech.FrontierA.isingDiagonalReflect_sub i j c x y a

/--
[hypercubicLattice_adj_diagonalReflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDiagonalReflectionGeometry.lean)
-/
@[path]
private lemma hypercubicLattice_adj_diagonalReflect_eq
  {d : Nat}
  {i j : Fin d}
  {c : Int}
  {x y : Site d}
-- given
  (hij : i ≠ j) :
-- imply
  (hypercubicLattice d).Adj x y <-> (hypercubicLattice d).Adj (isingDiagonalReflect i j c x) (isingDiagonalReflect i j c y) := by
-- proof
  apply StatMech.FrontierA.hypercubicLattice_adj_diagonalReflect i j hij c x y

/--
[isingDiagonalReflect_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDiagonalReflectionGeometry.lean)
-/
@[path]
private lemma isingDiagonalReflect_fixed_eq
  {d : Nat}
  {i j : Fin d}
  {c : Int}
  {x : Site d}
-- given
  (hij : i ≠ j)
  (hx : x i - x j = c) :
-- imply
  isingDiagonalReflect i j c x = x := by
-- proof
  apply StatMech.FrontierA.isingDiagonalReflect_fixed i j hij c x hx

/--
[isingDiagonalReflect_difference](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDiagonalReflectionGeometry.lean)
-/
@[path]
private lemma isingDiagonalReflect_difference_eq
  {d : Nat}
  {i j : Fin d}
  {c : Int}
  {x : Site d}
-- given
  (hij : i ≠ j) :
-- imply
  isingDiagonalReflect i j c x i - isingDiagonalReflect i j c x j = 2 * c - (x i - x j) := by
-- proof
  apply StatMech.FrontierA.isingDiagonalReflect_difference i j hij c x

/--
[diagonalDifference_adj_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDiagonalReflectionGeometry.lean)
-/
@[path]
private lemma diagonalDifference_adj_le_one_eq
  {d : Nat}
  {i j : Fin d}
  {x y : Site d}
-- given
  (hij : i ≠ j)
  (hxy : (hypercubicLattice d).Adj x y) :
-- imply
  (y i - y j - (x i - x j)).natAbs <= 1 := by
-- proof
  apply StatMech.FrontierA.diagonalDifference_adj_le_one i j hij hxy

/--
[diagonalPlane_separates_adjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDiagonalReflectionGeometry.lean)
-/
@[path]
private lemma diagonalPlane_separates_adjacent_eq
  {d : Nat}
  {i j : Fin d}
  {c : Int}
  {x y : Site d}
-- given
  (hij : i ≠ j)
  (hxy : (hypercubicLattice d).Adj x y)
  (hx : x i - x j < c)
  (hy : c < y i - y j) :
-- imply
  False := by
-- proof
  apply StatMech.FrontierA.diagonalPlane_separates_adjacent i j hij c hxy hx hy


-- created on 2026-10-23
