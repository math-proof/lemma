import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bkm_dccreroute
open Set SimpleGraph StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech StatMech.Walls


/--
[bkm_dcc_reroute](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkm_dccreroute.lean)
-/
@[path]
private lemma bkm_dcc_reroute_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a x : Site d}
  {w : (openSubgraph d (removeSite 0 ω)).Walk a x}
-- given
  (hx : x ≠ 0) :
-- imply
  (w.mapLe (ava_removeSite_openSubgraph_le ω)).support = w.support ∧ (0 : Site d) ∉ (w.mapLe (ava_removeSite_openSubgraph_le ω)).support := by
-- proof
  apply StatMech.Walls.bkm_dcc_reroute ω hx w

/--
[bkm_dcc_reroute_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkm_dccreroute.lean)
-/
@[path]
private lemma bkm_dcc_reroute_exists_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a x : Site d}
  {w : (openSubgraph d (removeSite 0 ω)).Walk a x}
-- given
  (hx : x ≠ 0) :
-- imply
  ∃ w' : (openSubgraph d ω).Walk a x, w'.support = w.support ∧ (0 : Site d) ∉ w'.support := by
-- proof
  apply StatMech.Walls.bkm_dcc_reroute_exists ω hx w

/--
[bkm_dcc_reroute_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkm_dccreroute.lean)
-/
@[path]
private lemma bkm_dcc_reroute_edges_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a x : Site d}
  {w : (openSubgraph d (removeSite 0 ω)).Walk a x}
-- given
  (hx : x ≠ 0) :
-- imply
  ∃ w' : (openSubgraph d ω).Walk a x, w'.support = w.support ∧ w'.edges = w.edges ∧ (0 : Site d) ∉ w'.support := by
-- proof
  apply StatMech.Walls.bkm_dcc_reroute_edges ω hx w


-- created on 2026-10-23
