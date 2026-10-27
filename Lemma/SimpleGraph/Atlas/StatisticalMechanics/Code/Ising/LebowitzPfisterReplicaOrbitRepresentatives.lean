import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRepresentatives.Part3
open Finset StatMech StatMech.Ising


/--
[lpReplicaCurrentEdgeRank_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRepresentatives.lean)
-/
@[path]
private lemma lpReplicaCurrentEdgeRank_injective_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V) :
-- imply
  Function.Injective (lpReplicaCurrentEdgeRank G sites) := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentEdgeRank_injective G sites

/--
[mem_lpReplicaCurrentEdgeOrbitReps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRepresentatives.lean)
-/
@[path]
private lemma mem_lpReplicaCurrentEdgeOrbitReps_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {e : (lpReplicaCurrentGraph G sites).edgeFinset}
-- given
  (sites : I -> V) :
-- imply
  e ∈ lpReplicaCurrentEdgeOrbitReps G sites ↔ lpReplicaCurrentEdgeRank G sites e <= lpReplicaCurrentEdgeRank G sites (lpReplicaCurrentEdgeReflect G sites e) := by
-- proof
  apply StatMech.Ising.mem_lpReplicaCurrentEdgeOrbitReps G sites e

/--
[lpReplicaCurrentEdge_mem_reps_or_reflect_mem_reps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRepresentatives.lean)
-/
@[path]
private lemma lpReplicaCurrentEdge_mem_reps_or_reflect_mem_reps_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {e : (lpReplicaCurrentGraph G sites).edgeFinset}
-- given
  (sites : I -> V) :
-- imply
  e ∈ lpReplicaCurrentEdgeOrbitReps G sites ∨ lpReplicaCurrentEdgeReflect G sites e ∈ lpReplicaCurrentEdgeOrbitReps G sites := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentEdge_mem_reps_or_reflect_mem_reps G sites e

/--
[lpReplicaCurrentEdge_eq_reflect_of_mem_reps_of_reflect_mem_reps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRepresentatives.lean)
-/
@[path]
private lemma lpReplicaCurrentEdge_eq_reflect_of_mem_reps_of_reflect_mem_reps_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {e : (lpReplicaCurrentGraph G sites).edgeFinset}
-- given
  (sites : I -> V)
  (he : e ∈ lpReplicaCurrentEdgeOrbitReps G sites)
  (hre : lpReplicaCurrentEdgeReflect G sites e ∈ lpReplicaCurrentEdgeOrbitReps G sites) :
-- imply
  e = lpReplicaCurrentEdgeReflect G sites e := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentEdge_eq_reflect_of_mem_reps_of_reflect_mem_reps G sites e he hre

/--
[lpReplicaCurrentEdge_mem_reps_iff_reflect_not_mem_reps_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRepresentatives.lean)
-/
@[path]
private lemma lpReplicaCurrentEdge_mem_reps_iff_reflect_not_mem_reps_of_ne_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {e : (lpReplicaCurrentGraph G sites).edgeFinset}
-- given
  (sites : I -> V)
  (hne : e ≠ lpReplicaCurrentEdgeReflect G sites e) :
-- imply
  e ∈ lpReplicaCurrentEdgeOrbitReps G sites ↔ lpReplicaCurrentEdgeReflect G sites e ∉ lpReplicaCurrentEdgeOrbitReps G sites := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentEdge_mem_reps_iff_reflect_not_mem_reps_of_ne G sites e hne

/--
[mem_lpReplicaCurrentEdgeOrbitStrictReps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRepresentatives.lean)
-/
@[path]
private lemma mem_lpReplicaCurrentEdgeOrbitStrictReps_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {e : (lpReplicaCurrentGraph G sites).edgeFinset}
-- given
  (sites : I -> V) :
-- imply
  e ∈ lpReplicaCurrentEdgeOrbitStrictReps G sites ↔ e ∈ lpReplicaCurrentEdgeOrbitReps G sites ∧ e ≠ lpReplicaCurrentEdgeReflect G sites e := by
-- proof
  apply StatMech.Ising.mem_lpReplicaCurrentEdgeOrbitStrictReps G sites e

/--
[mem_lpReplicaCurrentEdgeOrbitFixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRepresentatives.lean)
-/
@[path]
private lemma mem_lpReplicaCurrentEdgeOrbitFixed_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {e : (lpReplicaCurrentGraph G sites).edgeFinset}
-- given
  (sites : I -> V) :
-- imply
  e ∈ lpReplicaCurrentEdgeOrbitFixed G sites ↔ e = lpReplicaCurrentEdgeReflect G sites e := by
-- proof
  apply StatMech.Ising.mem_lpReplicaCurrentEdgeOrbitFixed G sites e

/--
[lpReplicaCurrentEdge_reflect_strictReps_eq_compl_reps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRepresentatives.lean)
-/
@[path]
private lemma lpReplicaCurrentEdge_reflect_strictReps_eq_compl_reps_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V) :
-- imply
  (lpReplicaCurrentEdgeOrbitStrictReps G sites).map (lpReplicaCurrentEdgeReflect G sites).toEmbedding = Finset.univ \ lpReplicaCurrentEdgeOrbitReps G sites := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentEdge_reflect_strictReps_eq_compl_reps G sites

/--
[lpReplicaCurrentEdge_univ_eq_fixed_union_reps_union_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRepresentatives.lean)
-/
@[path]
private lemma lpReplicaCurrentEdge_univ_eq_fixed_union_reps_union_reflect_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V) :
-- imply
  (Finset.univ : Finset (lpReplicaCurrentGraph G sites).edgeFinset) = lpReplicaCurrentEdgeOrbitFixed G sites ∪ (lpReplicaCurrentEdgeOrbitStrictReps G sites ∪ (lpReplicaCurrentEdgeOrbitStrictReps G sites).map (lpReplicaCurrentEdgeReflect G sites).toEmbedding) := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentEdge_univ_eq_fixed_union_reps_union_reflect G sites

/--
[lpReplicaCurrentEdge_fixed_subset_reps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRepresentatives.lean)
-/
@[path]
private lemma lpReplicaCurrentEdge_fixed_subset_reps_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V) :
-- imply
  lpReplicaCurrentEdgeOrbitFixed G sites ⊆ lpReplicaCurrentEdgeOrbitReps G sites := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentEdge_fixed_subset_reps G sites

/--
[lpReplicaCurrentEdge_strictReps_subset_reps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRepresentatives.lean)
-/
@[path]
private lemma lpReplicaCurrentEdge_strictReps_subset_reps_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V) :
-- imply
  lpReplicaCurrentEdgeOrbitStrictReps G sites ⊆ lpReplicaCurrentEdgeOrbitReps G sites := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentEdge_strictReps_subset_reps G sites

/--
[lpReplicaCurrentEdge_disjoint_reps_reflectStrictReps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRepresentatives.lean)
-/
@[path]
private lemma lpReplicaCurrentEdge_disjoint_reps_reflectStrictReps_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V) :
-- imply
  Disjoint (lpReplicaCurrentEdgeOrbitReps G sites) ((lpReplicaCurrentEdgeOrbitStrictReps G sites).map (lpReplicaCurrentEdgeReflect G sites).toEmbedding) := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentEdge_disjoint_reps_reflectStrictReps G sites

/--
[lpReplicaCurrentEdge_disjoint_strictReps_reflectStrictReps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRepresentatives.lean)
-/
@[path]
private lemma lpReplicaCurrentEdge_disjoint_strictReps_reflectStrictReps_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V) :
-- imply
  Disjoint (lpReplicaCurrentEdgeOrbitStrictReps G sites) ((lpReplicaCurrentEdgeOrbitStrictReps G sites).map (lpReplicaCurrentEdgeReflect G sites).toEmbedding) := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentEdge_disjoint_strictReps_reflectStrictReps G sites

/--
[lpReplicaCurrentEdge_disjoint_fixed_repsUnionReflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRepresentatives.lean)
-/
@[path]
private lemma lpReplicaCurrentEdge_disjoint_fixed_repsUnionReflect_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V) :
-- imply
  Disjoint (lpReplicaCurrentEdgeOrbitFixed G sites) (lpReplicaCurrentEdgeOrbitStrictReps G sites ∪ (lpReplicaCurrentEdgeOrbitStrictReps G sites).map (lpReplicaCurrentEdgeReflect G sites).toEmbedding) := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentEdge_disjoint_fixed_repsUnionReflect G sites

/--
[lpReplicaCurrentEdge_prod_orbitPairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRepresentatives.lean)
-/
@[path]
private lemma lpReplicaCurrentEdge_prod_orbitPairs_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [CommMonoid M]
-- given
  (sites : I -> V)
  (f : (lpReplicaCurrentGraph G sites).edgeFinset -> M) :
-- imply
  (∏ e, f e) = (∏ e ∈ lpReplicaCurrentEdgeOrbitFixed G sites, f e) * ∏ e ∈ lpReplicaCurrentEdgeOrbitStrictReps G sites, (f e * f (lpReplicaCurrentEdgeReflect G sites e)) := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentEdge_prod_orbitPairs G sites f


-- created on 2026-10-23
