import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.oc_crosstreequeryincident
open StatMech.Lattice StatMech StatMech.Walls


/--
[oc_crosstree_query_incident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_crosstreequeryincident.lean)
-/
@[path]
private lemma oc_crosstree_query_incident_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {o : V}
  {B C : Set V}
  {l : List E}
  {disc₀ : Finset V}
  {ω : ConfigSpace E}
  {i : E}
-- given
  (hdisc₀ : ∀ x ∈ disc₀, x ∈ B)
  (hi : i ∈ (crossTree endU endV o C l disc₀).queried ω) :
-- imply
  ConnOpenSet endU endV ω (endU i) B ∨ ConnOpenSet endU endV ω (endV i) B := by
-- proof
  apply StatMech.Walls.oc_crosstree_query_incident endU endV o B C l disc₀ hdisc₀ ω i hi

/--
[oc_crosstree_query_incident_eq_engine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_crosstreequeryincident.lean)
-/
@[path]
private lemma oc_crosstree_query_incident_eq_engine_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {o : V}
  {B C : Set V}
  {l : List E}
  {disc₀ : Finset V}
  {ω : ConfigSpace E}
  {i : E}
-- given
  (hdisc₀ : ∀ x ∈ disc₀, x ∈ B)
  (hi : i ∈ (crossTree endU endV o C l disc₀).queried ω) :
-- imply
  oc_crosstree_query_incident endU endV o B C l disc₀ hdisc₀ ω i hi = StatMech.OSSS.queried_crossTree_imp endU endV o B C l disc₀ hdisc₀ ω i hi := by
-- proof
  apply StatMech.Walls.oc_crosstree_query_incident_eq_engine endU endV o B C l disc₀ hdisc₀ ω i hi

/--
[oc_incidentCluster_of_queried_crossTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_crosstreequeryincident.lean)
-/
@[path]
private lemma oc_incidentCluster_of_queried_crossTree_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {o : V}
  {B C : Set V}
  {l : List E}
  {disc₀ : Finset V}
  {ω : ConfigSpace E}
  {i : E}
-- given
  (hdisc₀ : ∀ x ∈ disc₀, x ∈ B)
  (hi : i ∈ (crossTree endU endV o C l disc₀).queried ω) :
-- imply
  StatMech.OSSS.ReachDomination.IncidentCluster endU endV ω B i := by
-- proof
  apply StatMech.Walls.oc_incidentCluster_of_queried_crossTree endU endV o B C l disc₀ hdisc₀ ω i hi


-- created on 2026-10-23
