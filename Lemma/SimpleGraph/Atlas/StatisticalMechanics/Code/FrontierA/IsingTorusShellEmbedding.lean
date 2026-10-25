import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusShellEmbedding
open StatMech StatMech.FrontierA


/--
[isingTorusTwoPoint_embedded_le_axis_of_natAbs_coordinate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusShellEmbedding.lean)
-/
@[path]
private lemma isingTorusTwoPoint_embedded_le_axis_of_natAbs_coordinate_eq
  {d k : Nat}
  {i : Fin d}
  {beta : Real}
  {x : Site d}
  {r : Nat}
-- given
  (hbeta : 0 <= beta)
  (hr : r < 2 ^ (k + 1))
  (hxi : (x i).natAbs = r) :
-- imply
  isingTorusTwoPoint beta 0 (isingSiteToDyadicTorus k x) <= isingTorusTwoPoint (k := k) beta 0 (isingTorusCoordinateShift i r) := by
-- proof
  apply StatMech.FrontierA.isingTorusTwoPoint_embedded_le_axis_of_natAbs_coordinate i beta hbeta x r hr hxi

/--
[exists_natAbs_coordinate_eq_of_mem_boxSV_vbF](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusShellEmbedding.lean)
-/
@[path]
private lemma exists_natAbs_coordinate_eq_of_mem_boxSV_vbF_eq
  {d k : Nat}
  {n : Nat}
  {x : Site d}
-- given
  (hn : 1 <= n)
  (hx : x ∈ boxSV_vbF d n) :
-- imply
  ∃ i : Fin d, (x i).natAbs = n := by
-- proof
  apply StatMech.FrontierA.exists_natAbs_coordinate_eq_of_mem_boxSV_vbF hn x hx

/--
[exists_isingTorusTwoPoint_embedded_shell_le_axis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusShellEmbedding.lean)
-/
@[path]
private lemma exists_isingTorusTwoPoint_embedded_shell_le_axis_eq
  {d k : Nat}
  {beta : Real}
  {n : Nat}
  {x : Site d}
-- given
  (hbeta : 0 <= beta)
  (hn : 1 <= n)
  (hnHalf : n < 2 ^ (k + 1))
  (hx : x ∈ boxSV_vbF d n) :
-- imply
  ∃ i : Fin d, isingTorusTwoPoint beta 0 (isingSiteToDyadicTorus k x) <= isingTorusTwoPoint (k := k) beta 0 (isingTorusCoordinateShift i n) := by
-- proof
  apply StatMech.FrontierA.exists_isingTorusTwoPoint_embedded_shell_le_axis beta hbeta hn hnHalf x hx


-- created on 2026-10-23
