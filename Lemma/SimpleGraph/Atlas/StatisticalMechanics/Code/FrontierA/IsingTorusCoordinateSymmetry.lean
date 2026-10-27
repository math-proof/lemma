import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusCoordinateSymmetry
open Finset StatMech StatMech.FrontierA


/--
[isingTorusCoordinateSwap_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusCoordinateSymmetry.lean)
-/
@[path]
private lemma isingTorusCoordinateSwap_apply_eq
  {d k : Nat}
  {i j a : Fin d}
  {x : IsingDyadicTorus d k} :
-- imply
  isingTorusCoordinateSwap i j x a = x (Equiv.swap i j a) := by
-- proof
  apply StatMech.FrontierA.isingTorusCoordinateSwap_apply i j a x

/--
[isingTorusCoordinateSwap_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusCoordinateSymmetry.lean)
-/
@[path]
private lemma isingTorusCoordinateSwap_add_eq
  {d k : Nat}
  {i j : Fin d}
  {x y : IsingDyadicTorus d k} :
-- imply
  isingTorusCoordinateSwap i j (x + y) = isingTorusCoordinateSwap i j x + isingTorusCoordinateSwap i j y := by
-- proof
  apply StatMech.FrontierA.isingTorusCoordinateSwap_add i j x y

/--
[isingTorusCoordinateSwap_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusCoordinateSymmetry.lean)
-/
@[path]
private lemma isingTorusCoordinateSwap_step_eq
  {d k : Nat}
  {i j l : Fin d} :
-- imply
  isingTorusCoordinateSwap (k := k) i j (isingTorusStep l) = isingTorusStep (Equiv.swap i j l) := by
-- proof
  apply StatMech.FrontierA.isingTorusCoordinateSwap_step i j l

/--
[isingTorusCoordinateSwap_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusCoordinateSymmetry.lean)
-/
@[path]
private lemma isingTorusCoordinateSwap_involutive_eq
  {d k : Nat}
  {i j : Fin d}
  {x : IsingDyadicTorus d k} :
-- imply
  isingTorusCoordinateSwap i j (isingTorusCoordinateSwap i j x) = x := by
-- proof
  apply StatMech.FrontierA.isingTorusCoordinateSwap_involutive i j x

/--
[isingTorusGraph_adj_coordinateSwap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusCoordinateSymmetry.lean)
-/
@[path]
private lemma isingTorusGraph_adj_coordinateSwap_eq
  {d k : Nat}
  {i j : Fin d}
  {x y : IsingDyadicTorus d k} :
-- imply
  (isingTorusGraph d k).Adj x y ↔ (isingTorusGraph d k).Adj (isingTorusCoordinateSwap i j x) (isingTorusCoordinateSwap i j y) := by
-- proof
  apply StatMech.FrontierA.isingTorusGraph_adj_coordinateSwap i j x y

/--
[isingTorusTwoPoint_coordinateSwap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusCoordinateSymmetry.lean)
-/
@[path]
private lemma isingTorusTwoPoint_coordinateSwap_eq
  {d k : Nat}
  {i j : Fin d}
  {beta : Real}
  {x y : IsingDyadicTorus d k} :
-- imply
  isingTorusTwoPoint beta x y = isingTorusTwoPoint beta (isingTorusCoordinateSwap i j x) (isingTorusCoordinateSwap i j y) := by
-- proof
  apply StatMech.FrontierA.isingTorusTwoPoint_coordinateSwap i j beta x y

/--
[isingTorusCoordinateSwap_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusCoordinateSymmetry.lean)
-/
@[path]
private lemma isingTorusCoordinateSwap_zero_eq
  {d k : Nat}
  {i j : Fin d} :
-- imply
  isingTorusCoordinateSwap (k := k) i j 0 = 0 := by
-- proof
  apply StatMech.FrontierA.isingTorusCoordinateSwap_zero i j

/--
[isingTorusCoordinateSwap_coordinateShift_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusCoordinateSymmetry.lean)
-/
@[path]
private lemma isingTorusCoordinateSwap_coordinateShift_left_eq
  {d k : Nat}
  {i j : Fin d}
  {r : Nat} :
-- imply
  isingTorusCoordinateSwap (k := k) i j (isingTorusCoordinateShift i r) = isingTorusCoordinateShift j r := by
-- proof
  apply StatMech.FrontierA.isingTorusCoordinateSwap_coordinateShift_left i j r

/--
[isingTorusTwoPoint_axis_eq_axis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusCoordinateSymmetry.lean)
-/
@[path]
private lemma isingTorusTwoPoint_axis_eq_axis_eq
  {d k : Nat}
  {i j : Fin d}
  {beta : Real}
  {r : Nat} :
-- imply
  isingTorusTwoPoint (k := k) beta 0 (isingTorusCoordinateShift i r) = isingTorusTwoPoint (k := k) beta 0 (isingTorusCoordinateShift j r) := by
-- proof
  apply StatMech.FrontierA.isingTorusTwoPoint_axis_eq_axis i j beta r

/--
[isingTorusTwoPoint_embedded_shell_le_axis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusCoordinateSymmetry.lean)
-/
@[path]
private lemma isingTorusTwoPoint_embedded_shell_le_axis_eq
  {d k : Nat}
  {j : Fin d}
  {beta : Real}
  {n : Nat}
  {x : Site d}
-- given
  (hbeta : 0 <= beta)
  (hn : 1 <= n)
  (hnHalf : n < 2 ^ (k + 1))
  (hx : x ∈ boxSV_vbF d n) :
-- imply
  isingTorusTwoPoint beta 0 (isingSiteToDyadicTorus k x) <= isingTorusTwoPoint (k := k) beta 0 (isingTorusCoordinateShift j n) := by
-- proof
  apply StatMech.FrontierA.isingTorusTwoPoint_embedded_shell_le_axis j beta hbeta hn hnHalf x hx


-- created on 2026-10-23
