import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.KacWardTrivalentCoefficients
open StatMech StatMech.FrontierA


/--
[kw_cycleWeight_factor_of_disjoint_partition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardTrivalentCoefficients.lean)
-/
@[path]
private lemma kw_cycleWeight_factor_of_disjoint_partition_eq
  {V : Type u}
  [DecidableEq V]
  {R : Type v}
  [CommMonoid R]
  [Fintype ι]
  [DecidableEq ι]
  {F : Finset (Sym2 V)}
-- given
  (piece : ι -> Finset (Sym2 V))
  (weight : Sym2 V -> R)
  (hcover : F = Finset.univ.biUnion piece)
  (hdisj : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint piece) :
-- imply
  (∏ edge ∈ F, weight edge) = ∏ i, ∏ edge ∈ piece i, weight edge := by
-- proof
  apply StatMech.FrontierA.kw_cycleWeight_factor_of_disjoint_partition F piece weight hcover hdisj

/--
[kw_trivalent_even_cycle_weight_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardTrivalentCoefficients.lean)
-/
@[path]
private lemma kw_trivalent_even_cycle_weight_decomposition_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {F : Finset (Sym2 V)}
  {R : Type v}
  [CommMonoid R]
-- given
  (hdeg : ∀ vertex, G.degree vertex ≤ 3)
  (hF : F ∈ evenSubgraphs G)
  (weight : Sym2 V -> R) :
-- imply
  ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (base : ι -> V) (cycle : (i : ι) -> G.Walk (base i) (base i)), (∀ i, (cycle i).IsCycle) ∧ F = Finset.univ.biUnion (fun i => (cycle i).edges.toFinset) ∧ ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint (fun i => (cycle i).edges.toFinset) ∧ ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint (fun i => (cycle i).toSubgraph.verts) ∧ (∏ edge ∈ F, weight edge) = ∏ i, ∏ edge ∈ (cycle i).edges.toFinset, weight edge := by
-- proof
  apply StatMech.FrontierA.kw_trivalent_even_cycle_weight_decomposition G hdeg F hF weight


-- created on 2026-10-23
