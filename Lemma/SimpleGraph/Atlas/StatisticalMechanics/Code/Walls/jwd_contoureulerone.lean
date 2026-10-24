import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.jwd_contoureulerone
open SimpleGraph StatMech StatMech.Walls


/--
[jwd_cyclomaticNumber_eq_boundedRegionCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_contoureulerone.lean)
-/
@[path]
private lemma jwd_cyclomaticNumber_eq_boundedRegionCount_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [Fintype G.edgeSet]
-- given
  (hG : G.Connected) :
-- imply
  cyclomaticNumber G = jes_boundedRegionCount G := by
-- proof
  apply StatMech.Walls.jwd_cyclomaticNumber_eq_boundedRegionCount hG

/--
[jwd_cycleGraph_edgeSet_ncard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_contoureulerone.lean)
-/
@[path]
private lemma jwd_cycleGraph_edgeSet_ncard_eq
  {n : ℕ} :
-- imply
  (cycleGraph (n + 3)).edgeSet.ncard = n + 3 := by
-- proof
  apply StatMech.Walls.jwd_cycleGraph_edgeSet_ncard n

/--
[jwd_cycleGraph_boundedRegionCount_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_contoureulerone.lean)
-/
@[path]
private lemma jwd_cycleGraph_boundedRegionCount_one_eq
  {n : ℕ} :
-- imply
  jes_boundedRegionCount (cycleGraph (n + 3)) = 1 := by
-- proof
  apply StatMech.Walls.jwd_cycleGraph_boundedRegionCount_one n

/--
[jwd_cycleGraph_cyclomaticNumber_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_contoureulerone.lean)
-/
@[path]
private lemma jwd_cycleGraph_cyclomaticNumber_eq_one_eq
  {n : ℕ} :
-- imply
  cyclomaticNumber (cycleGraph (n + 3)) = 1 := by
-- proof
  apply StatMech.Walls.jwd_cycleGraph_cyclomaticNumber_eq_one n

/--
[contourEulerChar_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_contoureulerone.lean)
-/
@[path]
private lemma contourEulerChar_eq_one_eq
  {p : ℕ}
-- given
  (hp : 3 ≤ p) :
-- imply
  contourEulerChar p = 1 := by
-- proof
  apply StatMech.Walls.contourEulerChar_eq_one hp

/--
[contourEulerChar_eq_lattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_contoureulerone.lean)
-/
@[path]
private lemma contourEulerChar_eq_lattice_eq
  {p : ℕ} :
-- imply
  contourEulerChar p = StatMech.Lattice.contourEulerChar p := by
-- proof
  apply StatMech.Walls.contourEulerChar_eq_lattice p


-- created on 2026-10-23
