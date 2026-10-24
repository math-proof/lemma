import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.BoxConnectionFullConnection
open MeasureTheory SimpleGraph StatMech StatMech.FK


/--
[boxConnEvent_subset_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxConnectionFullConnection.lean)
-/
@[path]
private lemma boxConnEvent_subset_connected_eq
  {d n : Nat}
  {x y : boxVerts d n} :
-- imply
  boxConnEvent d n x y ⊆ {omega | StatMech.Lattice.Connected d omega x.1 y.1} := by
-- proof
  apply StatMech.FK.boxConnEvent_subset_connected d n x y

/--
[measureReal_boxConnEvent_le_infiniteTwoPointReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxConnectionFullConnection.lean)
-/
@[path]
private lemma measureReal_boxConnEvent_le_infiniteTwoPointReal_eq
  {d n : Nat}
  {mu : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))}
  {x y : boxVerts d n} :
-- imply
  (mu : Measure (ConfigSpace (Sym2 (Site d)))).real (boxConnEvent d n x y) ≤ infiniteTwoPointReal (mu : Measure (ConfigSpace (Sym2 (Site d)))) x.1 y.1 := by
-- proof
  apply StatMech.FK.measureReal_boxConnEvent_le_infiniteTwoPointReal d n mu x y


-- created on 2026-10-23
