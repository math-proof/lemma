import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.TriHexBrickPlanar
open SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[hexagonalBrickVertex_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickPlanar.lean)
-/
@[path]
private lemma hexagonalBrickVertex_injective_eq :
-- imply
  Function.Injective hexagonalBrickVertex := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalBrickVertex_injective

/--
[hexagonalBrickVertex_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickPlanar.lean)
-/
@[path]
private lemma hexagonalBrickVertex_adj_eq
  {u v : HexVertex}
-- given
  (huv : hexagonalGraph.Adj u v) :
-- imply
  (hypercubicLattice 2).Adj (hexagonalBrickVertex u) (hexagonalBrickVertex v) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalBrickVertex_adj huv

/--
[triHexPlanarFiniteStarPlanar_graph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickPlanar.lean)
-/
@[path]
private lemma triHexPlanarFiniteStarPlanar_graph_eq
  {n : Nat} :
-- imply
  (triHexPlanarFiniteStarPlanar n).G = triHexPlanarFiniteStarGraph n := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStarPlanar_graph n


-- created on 2026-10-23
