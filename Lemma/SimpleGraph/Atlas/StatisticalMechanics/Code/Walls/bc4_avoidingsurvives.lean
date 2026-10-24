import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc4_avoidingsurvives
open Set SimpleGraph StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech StatMech.Walls


/--
[bc4_adj_survives_origin_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc4_avoidingsurvives.lean)
-/
@[path]
private lemma bc4_adj_survives_origin_cut_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {u w : Site d}
-- given
  (hu : u ≠ 0)
  (hw : w ≠ 0)
  (hadj : (openSubgraph d ω).Adj u w) :
-- imply
  (openSubgraph d (removeSite 0 ω)).Adj u w := by
-- proof
  apply StatMech.Walls.bc4_adj_survives_origin_cut ω hu hw hadj

/--
[bc4_avoiding_walk_survives_origin_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc4_avoidingsurvives.lean)
-/
@[path]
private lemma bc4_avoiding_walk_survives_origin_cut_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {u w : Site d}
  {p : (openSubgraph d ω).Walk u w}
-- given
  (hp : (0 : Site d) ∉ p.support) :
-- imply
  Connected d (removeSite 0 ω) u w := by
-- proof
  apply StatMech.Walls.bc4_avoiding_walk_survives_origin_cut ω p hp

/--
[bc4_avoiding_survives_origin_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc4_avoidingsurvives.lean)
-/
@[path]
private lemma bc4_avoiding_survives_origin_cut_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {u w : Site d}
-- given
  (h : ∃ p : (openSubgraph d ω).Walk u w, (0 : Site d) ∉ p.support) :
-- imply
  Connected d (removeSite 0 ω) u w := by
-- proof
  apply StatMech.Walls.bc4_avoiding_survives_origin_cut ω h

/--
[bc4_cluster_mono_of_avoiding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc4_avoidingsurvives.lean)
-/
@[path]
private lemma bc4_cluster_mono_of_avoiding_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {u w : Site d}
  {p : (openSubgraph d ω).Walk u w}
-- given
  (hp : (0 : Site d) ∉ p.support) :
-- imply
  w ∈ cluster d (removeSite 0 ω) u := by
-- proof
  apply StatMech.Walls.bc4_cluster_mono_of_avoiding ω p hp

/--
[bc4_avoiding_walk_survives_origin_cut_singleEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc4_avoidingsurvives.lean)
-/
@[path]
private lemma bc4_avoiding_walk_survives_origin_cut_singleEdge_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {u w : Site d}
-- given
  (hu : u ≠ 0)
  (hw : w ≠ 0)
  (hadj : (openSubgraph d ω).Adj u w) :
-- imply
  Connected d (removeSite 0 ω) u w := by
-- proof
  apply StatMech.Walls.bc4_avoiding_walk_survives_origin_cut_singleEdge ω hu hw hadj


-- created on 2026-10-23
