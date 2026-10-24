import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.kc_latticeconnected
open Set SimpleGraph StatMech StatMech.Walls


/--
[kc_reach_axis_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_latticeconnected.lean)
-/
@[path]
private lemma kc_reach_axis_le_eq
  {d : ℕ}
  {x : Site d}
  {j : Fin d}
  {a : ℤ}
  {n : ℕ} :
-- imply
  (hypercubicLattice d).Reachable (Function.update x j a) (Function.update x j (a + (n : ℤ))) := by
-- proof
  apply StatMech.Walls.kc_reach_axis_le x j a n

/--
[kc_reach_axis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_latticeconnected.lean)
-/
@[path]
private lemma kc_reach_axis_eq
  {d : ℕ}
  {x : Site d}
  {j : Fin d}
  {a b : ℤ} :
-- imply
  (hypercubicLattice d).Reachable (Function.update x j a) (Function.update x j b) := by
-- proof
  apply StatMech.Walls.kc_reach_axis x j a b

/--
[kc_reach_all_d](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_latticeconnected.lean)
-/
@[path]
private lemma kc_reach_all_d_eq
  {d : ℕ}
  {x y : Site d} :
-- imply
  (hypercubicLattice d).Reachable x y := by
-- proof
  apply StatMech.Walls.kc_reach_all_d x y

/--
[kc_lattice_preconnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_latticeconnected.lean)
-/
@[path]
private lemma kc_lattice_preconnected_eq
  {d : ℕ} :
-- imply
  (hypercubicLattice d).Preconnected := by
-- proof
  apply StatMech.Walls.kc_lattice_preconnected

/--
[kc_lattice_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_latticeconnected.lean)
-/
@[path]
private lemma kc_lattice_connected_eq
  {d : ℕ} :
-- imply
  (hypercubicLattice d).Connected where preconnected := by
-- proof
  apply StatMech.Walls.kc_lattice_connected

/--
[kc_reach_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_latticeconnected.lean)
-/
@[path]
private lemma kc_reach_all_eq
  {d : ℕ}
  {x y : Site 2} :
-- imply
  (hypercubicLattice 2).Reachable x y := by
-- proof
  apply StatMech.Walls.kc_reach_all x y

/--
[kc_lattice2_preconnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_latticeconnected.lean)
-/
@[path]
private lemma kc_lattice2_preconnected_eq
  {d : ℕ} :
-- imply
  (hypercubicLattice 2).Preconnected := by
-- proof
  apply StatMech.Walls.kc_lattice2_preconnected

/--
[kc_lattice2_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_latticeconnected.lean)
-/
@[path]
private lemma kc_lattice2_connected_eq
  {d : ℕ} :
-- imply
  (hypercubicLattice 2).Connected := by
-- proof
  apply StatMech.Walls.kc_lattice2_connected


-- created on 2026-10-23
