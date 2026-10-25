import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusShellMonotonicity
open Finset StatMech StatMech.FrontierA


/--
[isingTorusTwoPoint_le_axis_of_coordinate_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusShellMonotonicity.lean)
-/
@[path]
private lemma isingTorusTwoPoint_le_axis_of_coordinate_eq_eq
  {d k : Nat}
  {i : Fin d}
  {beta : Real}
  {z : IsingDyadicTorus d k}
  {r : Nat}
-- given
  (hbeta : 0 <= beta)
  (hr : r < 2 ^ (k + 1))
  (hz : z i = (r : ZMod (2 ^ (k + 2)))) :
-- imply
  isingTorusTwoPoint beta 0 z <= isingTorusTwoPoint (k := k) beta 0 (isingTorusCoordinateShift i r) := by
-- proof
  apply StatMech.FrontierA.isingTorusTwoPoint_le_axis_of_coordinate_eq i beta hbeta z r hr hz


-- created on 2026-10-23
