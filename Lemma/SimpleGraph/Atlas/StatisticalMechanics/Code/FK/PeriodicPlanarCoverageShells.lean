import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverageShells
open Finset MeasureTheory Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicGraph.mem_canonicalConnectionShellPairs_dist](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoverageShells.lean)
-/
@[path]
private lemma mem_canonicalConnectionShellPairs_dist_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {n : Nat}
  {xy : P.BufferedVertex n × P.BufferedVertex n}
-- given
  (hxy : xy ∈ P.canonicalConnectionShellPairs n) :
-- imply
  n ≤ P.graph.dist xy.1.1 xy.2.1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.mem_canonicalConnectionShellPairs_dist P n xy hxy

/--
[PeriodicGraph.orbitShellCandidatePairs_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoverageShells.lean)
-/
@[path]
private lemma orbitShellCandidatePairs_card_le_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {n : Nat} :
-- imply
  (P.orbitShellCandidatePairs n).card ≤ (P.orbitBox n).card ^ 2 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.orbitShellCandidatePairs_card_le P n

/--
[PeriodicGraph.canonicalConnectionShellPairs_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoverageShells.lean)
-/
@[path]
private lemma canonicalConnectionShellPairs_card_le_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {n : Nat} :
-- imply
  (P.canonicalConnectionShellPairs n).card ≤ (81 * P.fundamentalDomain.card ^ 2) * (n + 1) ^ 4 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.canonicalConnectionShellPairs_card_le P n


-- created on 2026-10-23
