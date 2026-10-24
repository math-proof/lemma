import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.CylinderWidthLimit
open Filter Topology StatMech StatMech.Ising


/--
[antitone_cylinderWidthLimit_of_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CylinderWidthLimit.lean)
-/
@[path]
private lemma antitone_cylinderWidthLimit_of_diagonal_eq
  {M : Real}
-- given
  (a : Nat -> Nat -> Real)
  (m : Nat -> Real)
  (hwidth : forall H, Antitone (fun L => a L H))
  (hheight : forall L, Antitone (a L))
  (hrow : forall L, Tendsto (a L) atTop (nhds (m L)))
  (hdiag : Tendsto (fun L => a L L) atTop (nhds M)) :
-- imply
  Tendsto m atTop (nhds M) := by
-- proof
  apply StatMech.Ising.antitone_cylinderWidthLimit_of_diagonal a m M hwidth hheight hrow hdiag

/--
[monotone_cylinderWidthLimit_of_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CylinderWidthLimit.lean)
-/
@[path]
private lemma monotone_cylinderWidthLimit_of_diagonal_eq
  {M : Real}
-- given
  (a : Nat -> Nat -> Real)
  (m : Nat -> Real)
  (hwidth : forall H, Monotone (fun L => a L H))
  (hheight : forall L, Monotone (a L))
  (hrow : forall L, Tendsto (a L) atTop (nhds (m L)))
  (hdiag : Tendsto (fun L => a L L) atTop (nhds M)) :
-- imply
  Tendsto m atTop (nhds M) := by
-- proof
  apply StatMech.Ising.monotone_cylinderWidthLimit_of_diagonal a m M hwidth hheight hrow hdiag


-- created on 2026-10-23
