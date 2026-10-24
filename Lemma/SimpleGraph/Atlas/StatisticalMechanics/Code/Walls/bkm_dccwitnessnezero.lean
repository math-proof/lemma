import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bkm_dccwitnessnezero
open StatMech StatMech.Walls


/--
[bkm_origin_no_neighbour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkm_dccwitnessnezero.lean)
-/
@[path]
private lemma bkm_origin_no_neighbour_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {w : Site d} :
-- imply
  ¬ (openSubgraph d (removeSite 0 ω)).Adj 0 w := by
-- proof
  apply StatMech.Walls.bkm_origin_no_neighbour ω w

/--
[bkm_reachable_origin_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkm_dccwitnessnezero.lean)
-/
@[path]
private lemma bkm_reachable_origin_eq_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {y : Site d}
-- given
  (hy : Connected d (removeSite 0 ω) 0 y) :
-- imply
  y = 0 := by
-- proof
  apply StatMech.Walls.bkm_reachable_origin_eq ω hy

/--
[bkm_cluster_removeSite_origin_eq_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkm_dccwitnessnezero.lean)
-/
@[path]
private lemma bkm_cluster_removeSite_origin_eq_singleton_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  cluster d (removeSite 0 ω) 0 = {0} := by
-- proof
  apply StatMech.Walls.bkm_cluster_removeSite_origin_eq_singleton ω

/--
[bkm_cluster_removeSite_origin_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkm_dccwitnessnezero.lean)
-/
@[path]
private lemma bkm_cluster_removeSite_origin_finite_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  (cluster d (removeSite 0 ω) 0).Finite := by
-- proof
  apply StatMech.Walls.bkm_cluster_removeSite_origin_finite ω

/--
[bkm_cluster_removeSite_origin_not_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkm_dccwitnessnezero.lean)
-/
@[path]
private lemma bkm_cluster_removeSite_origin_not_infinite_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  ¬ (cluster d (removeSite 0 ω) 0).Infinite := by
-- proof
  apply StatMech.Walls.bkm_cluster_removeSite_origin_not_infinite ω

/--
[bkm_witness_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkm_dccwitnessnezero.lean)
-/
@[path]
private lemma bkm_witness_ne_zero_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {w : Site d}
-- given
  (hinf : (cluster d (removeSite 0 ω) w).Infinite) :
-- imply
  w ≠ 0 := by
-- proof
  apply StatMech.Walls.bkm_witness_ne_zero ω hinf

/--
[bkm_witnesses_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkm_dccwitnessnezero.lean)
-/
@[path]
private lemma bkm_witnesses_ne_zero_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : csc_DistinctClusterCorridors ω) :
-- imply
  ∃ (a₁ a₂ a₃ : Site d) (G : Finset (Sym2 (Site d))) (w₁ w₂ w₃ : Site d), (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧ ((hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧ (hypercubicLattice d).Adj 0 a₃) ∧ (Relation.ReflTransGen (CorridorStep G) a₁ w₁ ∧ Relation.ReflTransGen (CorridorStep G) a₂ w₂ ∧ Relation.ReflTransGen (CorridorStep G) a₃ w₃) ∧ ((cluster d (removeSite 0 (forceOpenFinset G ω)) w₁).Infinite ∧ (cluster d (removeSite 0 (forceOpenFinset G ω)) w₂).Infinite ∧ (cluster d (removeSite 0 (forceOpenFinset G ω)) w₃).Infinite) ∧ (¬ Connected d (removeSite 0 (forceOpenFinset G ω)) a₁ a₂ ∧ ¬ Connected d (removeSite 0 (forceOpenFinset G ω)) a₁ a₃ ∧ ¬ Connected d (removeSite 0 (forceOpenFinset G ω)) a₂ a₃) ∧ (w₁ ≠ 0 ∧ w₂ ≠ 0 ∧ w₃ ≠ 0) := by
-- proof
  apply StatMech.Walls.bkm_witnesses_ne_zero ω h


-- created on 2026-10-23
