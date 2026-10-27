import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarDuality
open Set StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[dualParam_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarDuality.lean)
-/
@[path]
private lemma dualParam_involutive_eq
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  dualParam (dualParam p q) q = p := by
-- proof
  apply StatMech.FK.PeriodicPlanar.dualParam_involutive hp hp1 hq

/--
[dual_parameter_boundary_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarDuality.lean)
-/
@[path]
private lemma dual_parameter_boundary_involutive_eq
  {p q : ℝ}
  {bc : BoundaryCondition}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  dualParam p q ∈ Ioo (0 : ℝ) 1 ∧ dualParam (dualParam p q) q = p ∧ RSW.dualBC (RSW.dualBC bc) = bc := by
-- proof
  apply StatMech.FK.PeriodicPlanar.dual_parameter_boundary_involutive hp hp1 hq bc

/--
[finite_planar_free_dual_exchange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarDuality.lean)
-/
@[path]
private lemma finite_planar_free_dual_exchange_eq
  {P : Lattice.PlanarZ2Subgraph}
  {omega : ConfigSpace (Sym2 P.V)}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  dualParam p q ∈ Ioo (0 : ℝ) 1 ∧ RSW.dualBC BoundaryCondition.free = BoundaryCondition.wired ∧ FK.fkProb P.G p q omega = pfdDualProb P (dualParam p q) q omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.finite_planar_free_dual_exchange P omega hp hp1 hq


-- created on 2026-10-23
