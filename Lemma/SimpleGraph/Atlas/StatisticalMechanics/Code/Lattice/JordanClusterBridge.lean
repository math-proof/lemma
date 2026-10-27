import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.JordanClusterBridge.Part8
open SimpleGraph Set StatMech StatMech.Lattice


/--
[jcb_boundedRegion_card_eq_nullity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanClusterBridge.lean)
-/
@[path]
private lemma jcb_boundedRegion_card_eq_nullity_eq
  {P : PlanarZ2Subgraph} :
-- imply
  Nat.card (jcb_BoundedRegion P) = nullity P.G := by
-- proof
  apply StatMech.Lattice.jcb_boundedRegion_card_eq_nullity P

/--
[jcb_nullity_eq_one_of_connected_card_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanClusterBridge.lean)
-/
@[path]
private lemma jcb_nullity_eq_one_of_connected_card_eq_eq
  {V : Type}
  [Empty.Finite V]
  {G : SimpleGraph V}
-- given
  (hconn : G.Connected)
  (hcard : G.edgeSet.ncard = Nat.card V) :
-- imply
  nullity G = 1 := by
-- proof
  apply StatMech.Lattice.jcb_nullity_eq_one_of_connected_card_eq G hconn hcard

/--
[jcb_boundedRegion_card_eq_one_of_nullity_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanClusterBridge.lean)
-/
@[path]
private lemma jcb_boundedRegion_card_eq_one_of_nullity_one_eq
  {P : PlanarZ2Subgraph}
-- given
  (h0 : nullity P.G = 1) :
-- imply
  Nat.card (jcb_BoundedRegion P) = 1 := by
-- proof
  apply StatMech.Lattice.jcb_boundedRegion_card_eq_one_of_nullity_one P h0

/--
[jcb_cyc4_edge_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanClusterBridge.lean)
-/
@[path]
private lemma jcb_cyc4_edge_card_eq :
-- imply
  jbc_cyc4.edgeSet.ncard = 4 := by
-- proof
  apply StatMech.Lattice.jcb_cyc4_edge_card

/--
[jcb_cyc4_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanClusterBridge.lean)
-/
@[path]
private lemma jcb_cyc4_connected_eq :
-- imply
  jbc_cyc4.Connected := by
-- proof
  apply StatMech.Lattice.jcb_cyc4_connected

/--
[jcb_square_nullity_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanClusterBridge.lean)
-/
@[path]
private lemma jcb_square_nullity_one_eq :
-- imply
  nullity jbc_Pce.G = 1 := by
-- proof
  apply StatMech.Lattice.jcb_square_nullity_one

/--
[jcb_square_uniqueBoundedRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanClusterBridge.lean)
-/
@[path]
private lemma jcb_square_uniqueBoundedRegion_eq :
-- imply
  Nat.card (jcb_BoundedRegion jbc_Pce) = 1 := by
-- proof
  apply StatMech.Lattice.jcb_square_uniqueBoundedRegion

/--
[jcb_Lemb_inj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanClusterBridge.lean)
-/
@[path]
private lemma jcb_Lemb_inj_eq :
-- imply
  Function.Injective jcb_Lemb := by
-- proof
  apply StatMech.Lattice.jcb_Lemb_inj

/--
[jcb_Lcyc_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanClusterBridge.lean)
-/
@[path]
private lemma jcb_Lcyc_adj_eq
  {i j : Fin 8} :
-- imply
  jcb_Lcyc.Adj i j ↔ jcb_LcycRel i j := by
-- proof
  apply StatMech.Lattice.jcb_Lcyc_adj i j

/--
[jcb_Lemb_isSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanClusterBridge.lean)
-/
@[path]
private lemma jcb_Lemb_isSub_eq :
-- imply
  ∀ ⦃i j : Fin 8⦄, jcb_Lcyc.Adj i j → (hypercubicLattice 2).Adj (jcb_Lemb i) (jcb_Lemb j) := by
-- proof
  apply StatMech.Lattice.jcb_Lemb_isSub

/--
[jcb_Lcyc_edge_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanClusterBridge.lean)
-/
@[path]
private lemma jcb_Lcyc_edge_card_eq :
-- imply
  jcb_Lcyc.edgeSet.ncard = 8 := by
-- proof
  apply StatMech.Lattice.jcb_Lcyc_edge_card

/--
[jcb_Lcyc_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanClusterBridge.lean)
-/
@[path]
private lemma jcb_Lcyc_connected_eq :
-- imply
  jcb_Lcyc.Connected := by
-- proof
  apply StatMech.Lattice.jcb_Lcyc_connected

/--
[jcb_Lshape_nullity_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanClusterBridge.lean)
-/
@[path]
private lemma jcb_Lshape_nullity_one_eq :
-- imply
  nullity jcb_LPce.G = 1 := by
-- proof
  apply StatMech.Lattice.jcb_Lshape_nullity_one

/--
[jcb_Lshape_uniqueBoundedRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanClusterBridge.lean)
-/
@[path]
private lemma jcb_Lshape_uniqueBoundedRegion_eq :
-- imply
  Nat.card (jcb_BoundedRegion jcb_LPce) = 1 := by
-- proof
  apply StatMech.Lattice.jcb_Lshape_uniqueBoundedRegion

/--
[jcb_diagK_not_kingSat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanClusterBridge.lean)
-/
@[path]
private lemma jcb_diagK_not_kingSat_eq :
-- imply
  ¬ npm_KingSaturated jcb_diagK := by
-- proof
  apply StatMech.Lattice.jcb_diagK_not_kingSat

/--
[jcb_diagK_not_own_starHull](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanClusterBridge.lean)
-/
@[path]
private lemma jcb_diagK_not_own_starHull_eq :
-- imply
  ndt_StarHull jcb_diagK ≠ jcb_diagK := by
-- proof
  apply StatMech.Lattice.jcb_diagK_not_own_starHull

/--
[jcb_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanClusterBridge.lean)
-/
@[path]
private lemma jcb_status_eq :
-- imply
  (∀ P : PlanarZ2Subgraph, Nat.card (jcb_BoundedRegion P) = nullity P.G) ∧ (∀ P : PlanarZ2Subgraph, nullity P.G = 1 → Nat.card (jcb_BoundedRegion P) = 1) ∧ Nat.card (jcb_BoundedRegion jbc_Pce) = 1 ∧ Nat.card (jcb_BoundedRegion jcb_LPce) = 1 ∧ ndt_StarHull jcb_diagK ≠ jcb_diagK := by
-- proof
  apply StatMech.Lattice.jcb_status


-- created on 2026-10-23
