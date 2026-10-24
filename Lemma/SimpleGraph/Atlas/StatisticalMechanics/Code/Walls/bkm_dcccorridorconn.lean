import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bkm_dcccorridorconn
open StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech.Percolation.DisjointPaths StatMech StatMech.Walls


/--
[bkm_dcc_corridor_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkm_dcccorridorconn.lean)
-/
@[path]
private lemma bkm_dcc_corridor_conn_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {G : Finset (Sym2 (Site d))}
  {p q : Site d}
-- given
  (h : Relation.ReflTransGen (CorridorStep G) p q) :
-- imply
  Connected d (removeSite 0 (forceOpenFinset G ω)) p q := by
-- proof
  apply StatMech.Walls.bkm_dcc_corridor_conn ω G h


-- created on 2026-10-23
