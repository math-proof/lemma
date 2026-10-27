import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonTrifurcation.Part2
open StatMech StatMech.FrontierA


/--
[mem_forestBranchVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonTrifurcation.lean)
-/
@[path]
private lemma mem_forestBranchVertices_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {v : V} :
-- imply
  v ∈ forestBranchVertices G ↔ 3 ≤ G.degree v := by
-- proof
  apply StatMech.FrontierA.mem_forestBranchVertices G v

/--
[mem_forestLeaves](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonTrifurcation.lean)
-/
@[path]
private lemma mem_forestLeaves_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {v : V} :
-- imply
  v ∈ forestLeaves G ↔ G.degree v = 1 := by
-- proof
  apply StatMech.FrontierA.mem_forestLeaves G v

/--
[finite_forest_branch_count_le_leaves](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonTrifurcation.lean)
-/
@[path]
private lemma finite_forest_branch_count_le_leaves_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (hacyclic : G.IsAcyclic)
  (hmin : ∀ v, 1 ≤ G.degree v) :
-- imply
  (forestBranchVertices G).card ≤ (forestLeaves G).card := by
-- proof
  apply StatMech.FrontierA.finite_forest_branch_count_le_leaves G hacyclic hmin

/--
[finite_forest_encounter_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonTrifurcation.lean)
-/
@[path]
private lemma finite_forest_encounter_count_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {T B : Finset V}
-- given
  (hacyclic : G.IsAcyclic)
  (hmin : ∀ v, 1 ≤ G.degree v)
  (hbranch : ∀ v ∈ T, 3 ≤ G.degree v)
  (hleaf : ∀ v, G.degree v = 1 → v ∈ B) :
-- imply
  T.card ≤ B.card := by
-- proof
  apply StatMech.FrontierA.finite_forest_encounter_count G hacyclic hmin T B hbranch hleaf

/--
[deleteVertex_openSubgraph_eq_removeSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonTrifurcation.lean)
-/
@[path]
private lemma deleteVertex_openSubgraph_eq_removeSite_eq
  [Fintype V]
  [Nonempty V]
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {x : Site d} :
-- imply
  bkg_deleteVertex (openSubgraph d omega) x = openSubgraph d (removeSite x omega) := by
-- proof
  apply StatMech.FrontierA.deleteVertex_openSubgraph_eq_removeSite omega x

/--
[fineTrifurcation_of_canonical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonTrifurcation.lean)
-/
@[path]
private lemma fineTrifurcation_of_canonical_eq
  [Fintype V]
  [Nonempty V]
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (h : IsCanonicalTrifurcation d omega x) :
-- imply
  bft_FineTrif omega x := by
-- proof
  apply StatMech.FrontierA.fineTrifurcation_of_canonical omega x h

/--
[mem_canonicalTrifurcationsInBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonTrifurcation.lean)
-/
@[path]
private lemma mem_canonicalTrifurcationsInBox_eq
  [Fintype V]
  [Nonempty V]
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {R : ℕ}
  {x : Site d} :
-- imply
  x ∈ canonicalTrifurcationsInBox omega R ↔ x ∈ box d (R - 1) ∧ IsCanonicalTrifurcation d omega x := by
-- proof
  apply StatMech.FrontierA.mem_canonicalTrifurcationsInBox

/--
[finite_canonical_trifurcation_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonTrifurcation.lean)
-/
@[path]
private lemma finite_canonical_trifurcation_count_eq
  [Fintype V]
  [Nonempty V]
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {R : ℕ}
-- given
  (hR : 1 ≤ R) :
-- imply
  (canonicalTrifurcationsInBox omega R).card ≤ (vertexBoundary_finite d R).toFinset.card := by
-- proof
  apply StatMech.FrontierA.finite_canonical_trifurcation_count omega R hR


-- created on 2026-10-23
