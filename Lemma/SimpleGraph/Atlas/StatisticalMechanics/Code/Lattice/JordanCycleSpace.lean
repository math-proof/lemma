import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.JordanCycleSpace.Part4
open SimpleGraph Set List Function StatMech StatMech.Lattice


/--
[jcs_support_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleSpace.lean)
-/
@[path]
private lemma jcs_support_card_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {v : V}
  {c : G.Walk v v}
-- given
  (hc : c.IsCycle) :
-- imply
  c.support.toFinset.card = c.length := by
-- proof
  apply StatMech.Lattice.jcs_support_card c hc

/--
[jcs_coe_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleSpace.lean)
-/
@[path]
private lemma jcs_coe_mem_eq
  {G : SimpleGraph V}
  {H : G.Subgraph}
  {e : Sym2 H.verts}
-- given
  (he : e ∈ H.coe.edgeSet) :
-- imply
  Sym2.map Subtype.val e ∈ H.edgeSet := by
-- proof
  apply StatMech.Lattice.jcs_coe_mem H e he

/--
[jcs_coe_mem'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleSpace.lean)
-/
@[path]
private lemma jcs_coe_mem'_eq
  {G : SimpleGraph V}
  {H : G.Subgraph}
  {e : Sym2 H.verts}
-- given
  (he : Sym2.map Subtype.val e ∈ H.edgeSet) :
-- imply
  e ∈ H.coe.edgeSet := by
-- proof
  apply StatMech.Lattice.jcs_coe_mem' H e he

/--
[jcs_coe_edge_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleSpace.lean)
-/
@[path]
private lemma jcs_coe_edge_card_eq
  {G : SimpleGraph V}
  {H : G.Subgraph} :
-- imply
  Nat.card H.coe.edgeSet = Nat.card H.edgeSet := by
-- proof
  apply StatMech.Lattice.jcs_coe_edge_card H

/--
[jcs_walk_edgeSet_ncard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleSpace.lean)
-/
@[path]
private lemma jcs_walk_edgeSet_ncard_eq
  {G : SimpleGraph V}
  {v : V}
  {c : G.Walk v v}
-- given
  (hc : c.IsCycle) :
-- imply
  c.edgeSet.ncard = c.length := by
-- proof
  apply StatMech.Lattice.jcs_walk_edgeSet_ncard c hc

/--
[jcs_cycle_nullity_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleSpace.lean)
-/
@[path]
private lemma jcs_cycle_nullity_eq_one_eq
  {G : SimpleGraph V}
  {v : V}
  {c : G.Walk v v}
-- given
  (hc : c.IsCycle) :
-- imply
  nullity c.toSubgraph.coe = 1 := by
-- proof
  apply StatMech.Lattice.jcs_cycle_nullity_eq_one c hc

/--
[jcs_cycle_faceCount_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleSpace.lean)
-/
@[path]
private lemma jcs_cycle_faceCount_eq_two_eq
  {G : SimpleGraph V}
  {v : V}
  {c : G.Walk v v}
-- given
  (hc : c.IsCycle) :
-- imply
  faceCount c.toSubgraph.coe = 2 := by
-- proof
  apply StatMech.Lattice.jcs_cycle_faceCount_eq_two c hc

/--
[jcs_cycle_euler](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleSpace.lean)
-/
@[path]
private lemma jcs_cycle_euler_eq
  {G : SimpleGraph V}
  {v : V}
  {c : G.Walk v v}
-- given
  (hc : c.IsCycle) :
-- imply
  (Nat.card ↑c.toSubgraph.verts : ℤ) - c.toSubgraph.coe.edgeSet.ncard + 2 = 1 + Nat.card c.toSubgraph.coe.ConnectedComponent := by
-- proof
  apply StatMech.Lattice.jcs_cycle_euler c hc

/--
[jcs_two_components_of_sides](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleSpace.lean)
-/
@[path]
private lemma jcs_two_components_of_sides_eq
  {S : Set (Site 2)}
  {x y : Site 2}
-- given
  (hx : x ∈ S)
  (hy : y ∉ S)
  (hin : ∀ a b : Site 2, a ∈ S → b ∈ S → (latticeMinusBarrier S).Reachable a b)
  (hout : ∀ a b : Site 2, a ∉ S → b ∉ S → (latticeMinusBarrier S).Reachable a b) :
-- imply
  Nat.card (latticeMinusBarrier S).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.jcs_two_components_of_sides S hx hy hin hout

/--
[jcs_two_components_of_region](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleSpace.lean)
-/
@[path]
private lemma jcs_two_components_of_region_eq
  {S : Set (Site 2)}
-- given
  (h : jcs_JordanRegion S) :
-- imply
  Nat.card (latticeMinusBarrier S).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.jcs_two_components_of_region h

/--
[jcs_separatingSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleSpace.lean)
-/
@[path]
private lemma jcs_separatingSide_eq
  {D B inside outside : Set (Site 2)}
  {S : Set (Site 2)}
-- given
  (hin : ∀ z ∈ inside, z ∈ S)
  (hout : ∀ z ∈ outside, z ∉ S)
  (hbd : ∀ u v : Site 2, u ∈ D → v ∈ D → (hypercubicLattice 2).Adj u v → u ∈ S → v ∉ S → (u ∈ B ∨ v ∈ B)) :
-- imply
  jcu_HasSeparatingSide D B inside outside := by
-- proof
  apply StatMech.Lattice.jcs_separatingSide S hin hout hbd

/--
[jcs_separatingSide_forces_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleSpace.lean)
-/
@[path]
private lemma jcs_separatingSide_forces_cross_eq
  {D B inside outside : Set (Site 2)}
  {S : Set (Site 2)}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (hinS : ∀ z ∈ inside, z ∈ S)
  (houtS : ∀ z ∈ outside, z ∉ S)
  (hbd : ∀ u v : Site 2, u ∈ D → v ∈ D → (hypercubicLattice 2).Adj u v → u ∈ S → v ∉ S → (u ∈ B ∨ v ∈ B))
  (hx : x ∈ inside)
  (hy : y ∈ outside)
  (hwD : ∀ z ∈ w.support, z ∈ D) :
-- imply
  ∃ z ∈ w.support, z ∈ B := by
-- proof
  apply StatMech.Lattice.jcs_separatingSide_forces_cross S hinS houtS hbd hx hy w hwD

/--
[jcs_cycle_two_components](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleSpace.lean)
-/
@[path]
private lemma jcs_cycle_two_components_eq
  {G : SimpleGraph V}
  {v : V}
  {c : G.Walk v v}
  {S : Set (Site 2)}
-- given
  (hc : c.IsCycle)
  (hbridge : jcs_GeometricBridge S) :
-- imply
  faceCount c.toSubgraph.coe = 2 ∧ Nat.card (latticeMinusBarrier S).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.jcs_cycle_two_components c hc S hbridge

/--
[jcs_separatingSide_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleSpace.lean)
-/
@[path]
private lemma jcs_separatingSide_of_bridge_eq
  {D B inside outside : Set (Site 2)}
  {S : Set (Site 2)}
-- given
  (hbridge : jcs_GeometricBridge S)
  (hinS : ∀ z ∈ inside, z ∈ S)
  (houtS : ∀ z ∈ outside, z ∉ S)
  (hbd : ∀ u v : Site 2, u ∈ D → v ∈ D → (hypercubicLattice 2).Adj u v → u ∈ S → v ∉ S → (u ∈ B ∨ v ∈ B)) :
-- imply
  jcu_HasSeparatingSide D B inside outside ∧ Nat.card (latticeMinusBarrier S).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.jcs_separatingSide_of_bridge S hbridge hinS houtS hbd


-- created on 2026-10-23
