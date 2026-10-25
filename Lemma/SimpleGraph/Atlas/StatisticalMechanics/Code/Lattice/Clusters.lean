import Mathlib
import sympy.Basic
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
open Set StatMech StatMech.Lattice


/--
[isOpenEdge_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Clusters.lean)
-/
@[path]
private lemma isOpenEdge_symm_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (h : IsOpenEdge d ω x y) :
-- imply
  IsOpenEdge d ω y x := by
-- proof
  apply StatMech.Lattice.isOpenEdge_symm h

/--
[isOpenEdge_irrefl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Clusters.lean)
-/
@[path]
private lemma isOpenEdge_irrefl_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d} :
-- imply
  ¬ IsOpenEdge d ω x x := by
-- proof
  apply StatMech.Lattice.isOpenEdge_irrefl x

/--
[isOpenEdge_imp_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Clusters.lean)
-/
@[path]
private lemma isOpenEdge_imp_adj_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (h : IsOpenEdge d ω x y) :
-- imply
  (hypercubicLattice d).Adj x y := by
-- proof
  apply StatMech.Lattice.isOpenEdge_imp_adj h

/--
[openSubgraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Clusters.lean)
-/
@[path]
private lemma openSubgraph_adj_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d} :
-- imply
  (openSubgraph d ω).Adj x y ↔ (hypercubicLattice d).Adj x y ∧ ω s(x, y) = true := by
-- proof
  apply StatMech.Lattice.openSubgraph_adj ω x y

/--
[openSubgraph_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Clusters.lean)
-/
@[path]
private lemma openSubgraph_le_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  openSubgraph d ω ≤ hypercubicLattice d := by
-- proof
  apply StatMech.Lattice.openSubgraph_le ω

/--
[connected_refl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Clusters.lean)
-/
@[path]
private lemma connected_refl_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d} :
-- imply
  Connected d ω x x := by
-- proof
  apply StatMech.Lattice.connected_refl ω x

/--
[connected_rfl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Clusters.lean)
-/
@[path]
private lemma connected_rfl_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d} :
-- imply
  Connected d ω x x := by
-- proof
  apply StatMech.Lattice.connected_rfl

/--
[Connected.symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Clusters.lean)
-/
@[path]
private lemma symm_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (h : Connected d ω x y) :
-- imply
  Connected d ω y x := by
-- proof
  apply StatMech.Lattice.Connected.symm h

/--
[Connected.trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Clusters.lean)
-/
@[path]
private lemma trans_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y z : Site d}
-- given
  (hxy : Connected d ω x y)
  (hyz : Connected d ω y z) :
-- imply
  Connected d ω x z := by
-- proof
  apply StatMech.Lattice.Connected.trans hxy hyz

/--
[connected_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Clusters.lean)
-/
@[path]
private lemma connected_comm_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d} :
-- imply
  Connected d ω x y ↔ Connected d ω y x := by
-- proof
  apply StatMech.Lattice.connected_comm

/--
[connected_equivalence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Clusters.lean)
-/
@[path]
private lemma connected_equivalence_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  Equivalence (Connected d ω) := by
-- proof
  apply StatMech.Lattice.connected_equivalence ω

/--
[IsOpenEdge.connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Clusters.lean)
-/
@[path]
private lemma connected_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (h : IsOpenEdge d ω x y) :
-- imply
  Connected d ω x y := by
-- proof
  apply StatMech.Lattice.IsOpenEdge.connected h

/--
[mem_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Clusters.lean)
-/
@[path]
private lemma mem_cluster_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d} :
-- imply
  y ∈ cluster d ω x ↔ Connected d ω x y := by
-- proof
  apply StatMech.Lattice.mem_cluster

/--
[self_mem_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Clusters.lean)
-/
@[path]
private lemma self_mem_cluster_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d} :
-- imply
  x ∈ cluster d ω x := by
-- proof
  apply StatMech.Lattice.self_mem_cluster ω x

/--
[cluster_eq_of_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Clusters.lean)
-/
@[path]
private lemma cluster_eq_of_connected_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (h : Connected d ω x y) :
-- imply
  cluster d ω x = cluster d ω y := by
-- proof
  apply StatMech.Lattice.cluster_eq_of_connected h

/--
[openSubgraphInduce_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Clusters.lean)
-/
@[path]
private lemma openSubgraphInduce_adj_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {S : Set (Site d)}
  {x y : S} :
-- imply
  (openSubgraphInduce d ω S).Adj x y ↔ (openSubgraph d ω).Adj x y := by
-- proof
  apply StatMech.Lattice.openSubgraphInduce_adj ω S x y

/--
[connectedWithin_refl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Clusters.lean)
-/
@[path]
private lemma connectedWithin_refl_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {S : Set (Site d)}
  {x : S} :
-- imply
  ConnectedWithin d ω S x x := by
-- proof
  apply StatMech.Lattice.connectedWithin_refl ω S x

/--
[ConnectedWithin.symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Clusters.lean)
-/
@[path]
private lemma symm_eq_2
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {S : Set (Site d)}
  {x y : S}
-- given
  (h : ConnectedWithin d ω S x y) :
-- imply
  ConnectedWithin d ω S y x := by
-- proof
  apply StatMech.Lattice.ConnectedWithin.symm h

/--
[ConnectedWithin.trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Clusters.lean)
-/
@[path]
private lemma trans_eq_2
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {S : Set (Site d)}
  {x y z : S}
-- given
  (hxy : ConnectedWithin d ω S x y)
  (hyz : ConnectedWithin d ω S y z) :
-- imply
  ConnectedWithin d ω S x z := by
-- proof
  apply StatMech.Lattice.ConnectedWithin.trans hxy hyz

/--
[ConnectedWithin.connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Clusters.lean)
-/
@[path]
private lemma connected_eq_2
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {S : Set (Site d)}
  {x y : S}
-- given
  (h : ConnectedWithin d ω S x y) :
-- imply
  Connected d ω x y := by
-- proof
  apply StatMech.Lattice.ConnectedWithin.connected h


-- created on 2026-10-23
