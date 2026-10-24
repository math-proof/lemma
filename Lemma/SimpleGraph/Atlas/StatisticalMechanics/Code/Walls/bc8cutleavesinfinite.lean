import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc8cutleavesinfinite
open Set SimpleGraph StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech StatMech.Walls


/--
[bc8_cutLeavesInfinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc8cutleavesinfinite.lean)
-/
@[path]
private lemma bc8_cutLeavesInfinite_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (hinf : (cluster d ω x).Infinite)
  (h0mem : (0 : Site d) ∈ cluster d ω x) :
-- imply
  ∃ n, (openSubgraph d ω).Adj 0 n ∧ (cluster d (removeSite 0 ω) n).Infinite := by
-- proof
  apply StatMech.Walls.bc8_cutLeavesInfinite ω hinf h0mem

/--
[bc8_cutLeavesInfinite_inCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc8cutleavesinfinite.lean)
-/
@[path]
private lemma bc8_cutLeavesInfinite_inCluster_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (hinf : (cluster d ω x).Infinite)
  (h0mem : (0 : Site d) ∈ cluster d ω x) :
-- imply
  ∃ n, (openSubgraph d ω).Adj 0 n ∧ n ∈ cluster d ω x ∧ (cluster d (removeSite 0 ω) n).Infinite := by
-- proof
  apply StatMech.Walls.bc8_cutLeavesInfinite_inCluster ω hinf h0mem

/--
[bc8_origin_openNeighbours_ncard_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc8cutleavesinfinite.lean)
-/
@[path]
private lemma bc8_origin_openNeighbours_ncard_le_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  {n : Site d | (openSubgraph d ω).Adj 0 n}.ncard ≤ 2 * d := by
-- proof
  apply StatMech.Walls.bc8_origin_openNeighbours_ncard_le ω

/--
[bc8_originCutLeavesInfinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc8cutleavesinfinite.lean)
-/
@[path]
private lemma bc8_originCutLeavesInfinite_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  bc3_OriginCutLeavesInfinite ω := by
-- proof
  apply StatMech.Walls.bc8_originCutLeavesInfinite ω

/--
[bc8_cutLeavesInfinite_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc8cutleavesinfinite.lean)
-/
@[path]
private lemma bc8_cutLeavesInfinite_origin_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hinf : (cluster d ω 0).Infinite) :
-- imply
  ∃ n, (openSubgraph d ω).Adj 0 n ∧ (cluster d (removeSite 0 ω) n).Infinite := by
-- proof
  apply StatMech.Walls.bc8_cutLeavesInfinite_origin ω hinf


-- created on 2026-10-23
