import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierB.BoxGraphPath
open Set SimpleGraph StatMech StatMech.FrontierB


/--
[setCoordinates_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoxGraphPath.lean)
-/
@[path]
private lemma setCoordinates_empty_eq
  {d : ℕ}
  {x y : Site d} :
-- imply
  setCoordinates x y ∅ = x := by
-- proof
  apply StatMech.FrontierB.setCoordinates_empty x y

/--
[setCoordinates_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoxGraphPath.lean)
-/
@[path]
private lemma setCoordinates_univ_eq
  {d : ℕ}
  {x y : Site d} :
-- imply
  setCoordinates x y Finset.univ = y := by
-- proof
  apply StatMech.FrontierB.setCoordinates_univ x y

/--
[setCoordinates_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoxGraphPath.lean)
-/
@[path]
private lemma setCoordinates_insert_eq
  {d : ℕ}
  {x y : Site d}
  {T : Finset (Fin d)}
  {j : Fin d}
-- given
  (hj : j ∉ T) :
-- imply
  setCoordinates x y (insert j T) = Function.update (setCoordinates x y T) j (y j) := by
-- proof
  apply StatMech.FrontierB.setCoordinates_insert x y T j hj

/--
[setCoordinates_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoxGraphPath.lean)
-/
@[path]
private lemma setCoordinates_mem_box_eq
  {d n : ℕ}
  {x y : Site d}
  {T : Finset (Fin d)}
-- given
  (hx : x ∈ box d n)
  (hy : y ∈ box d n) :
-- imply
  setCoordinates x y T ∈ box d n := by
-- proof
  apply StatMech.FrontierB.setCoordinates_mem_box hx hy T

/--
[box_reachable_setCoordinates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoxGraphPath.lean)
-/
@[path]
private lemma box_reachable_setCoordinates_eq
  {d n : ℕ}
  {x y : Site d}
  {T : Finset (Fin d)}
-- given
  (hx : x ∈ box d n)
  (hy : y ∈ box d n) :
-- imply
  ((hypercubicLattice d).induce (box d n)).Reachable ⟨x, hx⟩ ⟨setCoordinates x y T, setCoordinates_mem_box hx hy T⟩ := by
-- proof
  apply StatMech.FrontierB.box_reachable_setCoordinates x y hx hy T

/--
[boxGraph_preconnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoxGraphPath.lean)
-/
@[path]
private lemma boxGraph_preconnected_eq
  {d n : ℕ} :
-- imply
  (StatMech.FK.boxGraph d n).Preconnected := by
-- proof
  apply StatMech.FrontierB.boxGraph_preconnected d n

/--
[boxGraphPath_isPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoxGraphPath.lean)
-/
@[path]
private lemma boxGraphPath_isPath_eq
  {d n : ℕ}
  {x y : StatMech.FK.boxVerts d n} :
-- imply
  (boxGraphPath d n x y).IsPath := by
-- proof
  apply StatMech.FrontierB.boxGraphPath_isPath d n x y


-- created on 2026-10-23
