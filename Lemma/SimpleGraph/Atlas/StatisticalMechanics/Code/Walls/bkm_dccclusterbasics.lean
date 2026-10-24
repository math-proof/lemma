import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bkm_dccclusterbasics
open StatMech StatMech.Walls


/--
[bkm_removeSiteCluster_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkm_dccclusterbasics.lean)
-/
@[path]
private lemma bkm_removeSiteCluster_step_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x z : Site d}
  {u v : Site d}
-- given
  (hu : u ∈ cluster d (removeSite x ω) z)
  (hadj : (openSubgraph d (removeSite x ω)).Adj u v) :
-- imply
  v ∈ cluster d (removeSite x ω) z := by
-- proof
  apply StatMech.Walls.bkm_removeSiteCluster_step ω x z hu hadj

/--
[bkm_removeSiteCluster_step_isOpenEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkm_dccclusterbasics.lean)
-/
@[path]
private lemma bkm_removeSiteCluster_step_isOpenEdge_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x z : Site d}
  {u v : Site d}
-- given
  (hu : u ∈ cluster d (removeSite x ω) z)
  (hopen : IsOpenEdge d (removeSite x ω) u v) :
-- imply
  v ∈ cluster d (removeSite x ω) z := by
-- proof
  apply StatMech.Walls.bkm_removeSiteCluster_step_isOpenEdge ω x z hu hopen

/--
[bkm_removeSiteClusters_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkm_dccclusterbasics.lean)
-/
@[path]
private lemma bkm_removeSiteClusters_disjoint_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {x' y' : Site d}
-- given
  (h : ¬ Connected d (removeSite x ω) x' y') :
-- imply
  Disjoint (cluster d (removeSite x ω) x') (cluster d (removeSite x ω) y') := by
-- proof
  apply StatMech.Walls.bkm_removeSiteClusters_disjoint ω x h

/--
[bkm_removeSite0Clusters_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkm_dccclusterbasics.lean)
-/
@[path]
private lemma bkm_removeSite0Clusters_disjoint_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x' y' : Site d}
-- given
  (h : ¬ Connected d (removeSite 0 ω) x' y') :
-- imply
  Disjoint (cluster d (removeSite 0 ω) x') (cluster d (removeSite 0 ω) y') := by
-- proof
  apply StatMech.Walls.bkm_removeSite0Clusters_disjoint ω h


-- created on 2026-10-23
