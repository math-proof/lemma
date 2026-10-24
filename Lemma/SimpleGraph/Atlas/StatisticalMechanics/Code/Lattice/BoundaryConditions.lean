import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.BoundaryConditions
open StatMech StatMech.Lattice StatMech.Lattice.BoundaryCondition


/--
[free_ne_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoundaryConditions.lean)
-/
@[path]
private lemma free_ne_wired_eq :
-- imply
  (free ≠ wired) := by
-- proof
  apply StatMech.Lattice.BoundaryCondition.free_ne_wired

/--
[free_ne_periodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoundaryConditions.lean)
-/
@[path]
private lemma free_ne_periodic_eq :
-- imply
  (free ≠ periodic) := by
-- proof
  apply StatMech.Lattice.BoundaryCondition.free_ne_periodic

/--
[wired_ne_periodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoundaryConditions.lean)
-/
@[path]
private lemma wired_ne_periodic_eq :
-- imply
  (wired ≠ periodic) := by
-- proof
  apply StatMech.Lattice.BoundaryCondition.wired_ne_periodic

/--
[isOpen_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoundaryConditions.lean)
-/
@[path]
private lemma isOpen_symm_eq
  [Fintype V]
  [DecidableEq V]
  {ω : Sym2 V → Bool}
  {x y : V}
-- given
  (h : IsOpen G ω x y) :
-- imply
  IsOpen G ω y x := by
-- proof
  apply StatMech.Lattice.isOpen_symm h

/--
[isOpen_irrefl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoundaryConditions.lean)
-/
@[path]
private lemma isOpen_irrefl_eq
  [Fintype V]
  [DecidableEq V]
  {ω : Sym2 V → Bool}
  {x : V} :
-- imply
  ¬ IsOpen G ω x x := by
-- proof
  apply StatMech.Lattice.isOpen_irrefl x

/--
[openGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoundaryConditions.lean)
-/
@[path]
private lemma openGraph_adj_eq
  [Fintype V]
  [DecidableEq V]
  {ω : Sym2 V → Bool}
  {x y : V} :
-- imply
  (openGraph G ω).Adj x y ↔ G.Adj x y ∧ ω s(x, y) = true := by
-- proof
  apply StatMech.Lattice.openGraph_adj ω x y

/--
[openGraph_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoundaryConditions.lean)
-/
@[path]
private lemma openGraph_le_eq
  [Fintype V]
  [DecidableEq V]
  {ω : Sym2 V → Bool} :
-- imply
  openGraph G ω ≤ G := by
-- proof
  apply StatMech.Lattice.openGraph_le ω

/--
[numClustersFree_eq_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoundaryConditions.lean)
-/
@[path]
private lemma numClustersFree_eq_card_eq
  [Fintype V]
  [DecidableEq V]
  {ω : Sym2 V → Bool} :
-- imply
  numClustersFree G ω = Fintype.card (openGraph G ω).ConnectedComponent := by
-- proof
  apply StatMech.Lattice.numClustersFree_eq_card ω

/--
[boundaryCliqueGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoundaryConditions.lean)
-/
@[path]
private lemma boundaryCliqueGraph_adj_eq
  [Fintype V]
  [DecidableEq V]
  [DecidablePred bdry]
  {x y : V}
-- given
  (bdry : V → Prop) :
-- imply
  (boundaryCliqueGraph bdry).Adj x y ↔ x ≠ y ∧ bdry x ∧ bdry y := by
-- proof
  apply StatMech.Lattice.boundaryCliqueGraph_adj bdry x y

/--
[wiredGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoundaryConditions.lean)
-/
@[path]
private lemma wiredGraph_adj_eq
  [Fintype V]
  [DecidableEq V]
  [DecidablePred bdry]
  {ω : Sym2 V → Bool}
  {x y : V}
-- given
  (bdry : V → Prop) :
-- imply
  (wiredGraph G bdry ω).Adj x y ↔ (G.Adj x y ∧ ω s(x, y) = true) ∨ (x ≠ y ∧ bdry x ∧ bdry y) := by
-- proof
  apply StatMech.Lattice.wiredGraph_adj bdry ω x y

/--
[openGraph_le_wiredGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoundaryConditions.lean)
-/
@[path]
private lemma openGraph_le_wiredGraph_eq
  [Fintype V]
  [DecidableEq V]
  [DecidablePred bdry]
  {ω : Sym2 V → Bool}
-- given
  (bdry : V → Prop) :
-- imply
  openGraph G ω ≤ wiredGraph G bdry ω := by
-- proof
  apply StatMech.Lattice.openGraph_le_wiredGraph bdry ω

/--
[wiredGraph_adj_of_bdry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoundaryConditions.lean)
-/
@[path]
private lemma wiredGraph_adj_of_bdry_eq
  [Fintype V]
  [DecidableEq V]
  [DecidablePred bdry]
  {ω : Sym2 V → Bool}
  {x y : V}
-- given
  (bdry : V → Prop)
  (hne : x ≠ y)
  (hx : bdry x)
  (hy : bdry y) :
-- imply
  (wiredGraph G bdry ω).Adj x y := by
-- proof
  apply StatMech.Lattice.wiredGraph_adj_of_bdry bdry hne hx hy

/--
[numClustersWired_eq_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoundaryConditions.lean)
-/
@[path]
private lemma numClustersWired_eq_card_eq
  [Fintype V]
  [DecidableEq V]
  [DecidablePred bdry]
  {ω : Sym2 V → Bool}
-- given
  (bdry : V → Prop) :
-- imply
  numClustersWired G bdry ω = Fintype.card (wiredGraph G bdry ω).ConnectedComponent := by
-- proof
  apply StatMech.Lattice.numClustersWired_eq_card bdry ω

/--
[numClustersWired_le_numClustersFree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoundaryConditions.lean)
-/
@[path]
private lemma numClustersWired_le_numClustersFree_eq
  [Fintype V]
  [DecidableEq V]
  [DecidablePred bdry]
  {ω : Sym2 V → Bool}
-- given
  (bdry : V → Prop) :
-- imply
  numClustersWired G bdry ω ≤ numClustersFree G ω := by
-- proof
  apply StatMech.Lattice.numClustersWired_le_numClustersFree bdry ω

/--
[numClusters_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoundaryConditions.lean)
-/
@[path]
private lemma numClusters_free_eq
  [Fintype V]
  [DecidableEq V]
  [DecidablePred bdry]
  {ω : Sym2 V → Bool}
-- given
  (bdry : V → Prop) :
-- imply
  numClusters G bdry BoundaryCondition.free ω = numClustersFree G ω := by
-- proof
  apply StatMech.Lattice.numClusters_free bdry ω

/--
[numClusters_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoundaryConditions.lean)
-/
@[path]
private lemma numClusters_wired_eq
  [Fintype V]
  [DecidableEq V]
  [DecidablePred bdry]
  {ω : Sym2 V → Bool}
-- given
  (bdry : V → Prop) :
-- imply
  numClusters G bdry BoundaryCondition.wired ω = numClustersWired G bdry ω := by
-- proof
  apply StatMech.Lattice.numClusters_wired bdry ω

/--
[numClusters_periodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoundaryConditions.lean)
-/
@[path]
private lemma numClusters_periodic_eq
  [Fintype V]
  [DecidableEq V]
  [DecidablePred bdry]
  {ω : Sym2 V → Bool}
-- given
  (bdry : V → Prop) :
-- imply
  numClusters G bdry BoundaryCondition.periodic ω = numClustersFree G ω := by
-- proof
  apply StatMech.Lattice.numClusters_periodic bdry ω

/--
[numClusters_wired_le_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoundaryConditions.lean)
-/
@[path]
private lemma numClusters_wired_le_free_eq
  [Fintype V]
  [DecidableEq V]
  [DecidablePred bdry]
  {ω : Sym2 V → Bool}
-- given
  (bdry : V → Prop) :
-- imply
  numClusters G bdry BoundaryCondition.wired ω ≤ numClusters G bdry BoundaryCondition.free ω := by
-- proof
  apply StatMech.Lattice.numClusters_wired_le_free bdry ω


-- created on 2026-10-23
