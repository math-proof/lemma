import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.TreeNonBridgeProve.Part4
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[tnbp_reroute_avoiding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNonBridgeProve.lean)
-/
@[path]
private lemma tnbp_reroute_avoiding_eq
  {G G' : SimpleGraph V}
  {c : V}
-- given
  (hG' : ∀ a b, G'.Adj a b ↔ G.Adj a b ∧ a ≠ c ∧ b ≠ c)
  (hneigh : ∀ p q, G.Adj c p → G.Adj c q → G'.Reachable p q) :
-- imply
  ∀ {x y : V} (_w : G.Walk x y) (a : V), a ≠ c → (x = c → G.Adj a c) → (x ≠ c → G'.Reachable a x) → y ≠ c → G'.Reachable a y := by
-- proof
  apply StatMech.Lattice.tnbp_reroute_avoiding G G' c hG' hneigh

/--
[tnbp_reachable_of_avoid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNonBridgeProve.lean)
-/
@[path]
private lemma tnbp_reachable_of_avoid_eq
  {G G' : SimpleGraph V}
  {c : V}
  {x y : V}
-- given
  (hG' : ∀ a b, G'.Adj a b ↔ G.Adj a b ∧ a ≠ c ∧ b ≠ c)
  (hneigh : ∀ p q, G.Adj c p → G.Adj c q → G'.Reachable p q)
  (hx : x ≠ c)
  (hy : y ≠ c)
  (hr : G.Reachable x y) :
-- imply
  G'.Reachable x y := by
-- proof
  apply StatMech.Lattice.tnbp_reachable_of_avoid G G' c hG' hneigh hx hy hr

/--
[tnbp_insert_adj_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNonBridgeProve.lean)
-/
@[path]
private lemma tnbp_insert_adj_iff_eq
  {c : Site 2}
  {B : Set (Site 2)}
  {a b : Site 2} :
-- imply
  (ffc_offSupportLattice (insert c B)).Adj a b ↔ (ffc_offSupportLattice B).Adj a b ∧ a ≠ c ∧ b ≠ c := by
-- proof
  apply StatMech.Lattice.tnbp_insert_adj_iff c B a b

/--
[tnbp_reachable_insert_of_ringConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNonBridgeProve.lean)
-/
@[path]
private lemma tnbp_reachable_insert_of_ringConnected_eq
  {c : Site 2}
  {B : Set (Site 2)}
  {x y : Site 2}
-- given
  (hring : tnbp_RingConnected c B)
  (hx : x ≠ c)
  (hy : y ≠ c)
  (hr : (ffc_offSupportLattice B).Reachable x y) :
-- imply
  (ffc_offSupportLattice (insert c B)).Reachable x y := by
-- proof
  apply StatMech.Lattice.tnbp_reachable_insert_of_ringConnected hring hx hy hr

/--
[tnbp_step_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNonBridgeProve.lean)
-/
@[path]
private lemma tnbp_step_reachable_eq
  {B' : Set (Site 2)}
  {a b : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj a b)
  (ha : a ∉ B')
  (hb : b ∉ B') :
-- imply
  (ffc_offSupportLattice B').Reachable a b := by
-- proof
  apply StatMech.Lattice.tnbp_step_reachable B' hadj ha hb

/--
[tnbp_neighbour_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNonBridgeProve.lean)
-/
@[path]
private lemma tnbp_neighbour_cases_eq
  {c p : Site 2}
-- given
  (h : (hypercubicLattice 2).Adj c p) :
-- imply
  p = ![c 0 + 1, c 1] ∨ p = ![c 0 - 1, c 1] ∨ p = ![c 0, c 1 + 1] ∨ p = ![c 0, c 1 - 1] := by
-- proof
  apply StatMech.Lattice.tnbp_neighbour_cases h

/--
[tnbp_neighbours_to_ref](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNonBridgeProve.lean)
-/
@[path]
private lemma tnbp_neighbours_to_ref_eq
  {c : Site 2}
  {B : Set (Site 2)}
-- given
  (h : tnbp_RingClear c B) :
-- imply
  (ffc_offSupportLattice (insert c B)).Reachable ![c 0 - 1, c 1] ![c 0 + 1, c 1] ∧ (ffc_offSupportLattice (insert c B)).Reachable ![c 0, c 1 + 1] ![c 0 + 1, c 1] ∧ (ffc_offSupportLattice (insert c B)).Reachable ![c 0, c 1 - 1] ![c 0 + 1, c 1] := by
-- proof
  apply StatMech.Lattice.tnbp_neighbours_to_ref h

/--
[tnbp_neighbours_connected_of_ringClear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNonBridgeProve.lean)
-/
@[path]
private lemma tnbp_neighbours_connected_of_ringClear_eq
  {c : Site 2}
  {B : Set (Site 2)}
-- given
  (h : tnbp_RingClear c B) :
-- imply
  tnbp_RingConnected c B := by
-- proof
  apply StatMech.Lattice.tnbp_neighbours_connected_of_ringClear h

/--
[tnbp_exterior_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNonBridgeProve.lean)
-/
@[path]
private lemma tnbp_exterior_notMem_eq
  {B' : Set (Site 2)}
  {R : ℕ}
  {e : Site 2}
-- given
  (hB : B' ⊆ box 2 R)
  (he : e ∈ exterior 2 R) :
-- imply
  e ∉ B' := by
-- proof
  apply StatMech.Lattice.tnbp_exterior_notMem hB he

/--
[tnbp_reachesExterior_insert_of_ringConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNonBridgeProve.lean)
-/
@[path]
private lemma tnbp_reachesExterior_insert_of_ringConnected_eq
  {B : Set (Site 2)}
  {R : ℕ}
  {c : Site 2}
-- given
  (hbase : arcxc_ReachesExterior B R)
  (hc : c ∈ box 2 R)
  (hring : tnbp_RingConnected c B) :
-- imply
  arcxc_ReachesExterior (insert c B) R := by
-- proof
  apply StatMech.Lattice.tnbp_reachesExterior_insert_of_ringConnected hbase hc hring

/--
[tnbp_empty_reachesExterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNonBridgeProve.lean)
-/
@[path]
private lemma tnbp_empty_reachesExterior_eq
  {R : ℕ} :
-- imply
  arcxc_ReachesExterior (∅ : Set (Site 2)) R := by
-- proof
  apply StatMech.Lattice.tnbp_empty_reachesExterior R

/--
[tnbp_ringChain_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNonBridgeProve.lean)
-/
@[path]
private lemma tnbp_ringChain_nil_eq :
-- imply
  tnbp_RingChain [] := by
-- proof
  apply StatMech.Lattice.tnbp_ringChain_nil

/--
[tnbp_ringChain_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNonBridgeProve.lean)
-/
@[path]
private lemma tnbp_ringChain_cons_eq
  {c : Site 2}
  {L' : List (Site 2)}
-- given
  (hhead : tnbp_RingConnected c {x : Site 2 | x ∈ L'})
  (htail : tnbp_RingChain L') :
-- imply
  tnbp_RingChain (c :: L') := by
-- proof
  apply StatMech.Lattice.tnbp_ringChain_cons hhead htail

/--
[tnbp_reachesExterior_ringChain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNonBridgeProve.lean)
-/
@[path]
private lemma tnbp_reachesExterior_ringChain_eq
  {R : ℕ} :
-- imply
  ∀ {L : List (Site 2)}, (∀ c ∈ L, c ∈ box 2 R) → tnbp_RingChain L → arcxc_ReachesExterior {x : Site 2 | x ∈ L} R := by
-- proof
  apply StatMech.Lattice.tnbp_reachesExterior_ringChain

/--
[tnbp_ringClear_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNonBridgeProve.lean)
-/
@[path]
private lemma tnbp_ringClear_singleton_eq
  {c : Site 2} :
-- imply
  tnbp_RingClear c (∅ : Set (Site 2)) := by
-- proof
  apply StatMech.Lattice.tnbp_ringClear_singleton c

/--
[tnbp_ringChain_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNonBridgeProve.lean)
-/
@[path]
private lemma tnbp_ringChain_singleton_eq
  {c : Site 2} :
-- imply
  tnbp_RingChain [c] := by
-- proof
  apply StatMech.Lattice.tnbp_ringChain_singleton c

/--
[tnbp_singlePoint_reachesExterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNonBridgeProve.lean)
-/
@[path]
private lemma tnbp_singlePoint_reachesExterior_eq
  {c : Site 2}
  {R : ℕ}
-- given
  (hc : c ∈ box 2 R) :
-- imply
  arcxc_ReachesExterior ({c} : Set (Site 2)) R := by
-- proof
  apply StatMech.Lattice.tnbp_singlePoint_reachesExterior hc

/--
[tnbp_singlePoint_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNonBridgeProve.lean)
-/
@[path]
private lemma tnbp_singlePoint_connected_eq
  {c : Site 2} :
-- imply
  arcns_OffSupportConnected ({c} : Set (Site 2)) := by
-- proof
  apply StatMech.Lattice.tnbp_singlePoint_connected c

/--
[tnbp_singlePoint_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNonBridgeProve.lean)
-/
@[path]
private lemma tnbp_singlePoint_nonvacuous_eq :
-- imply
  (ffc_offSupportLattice ({![0, 0]} : Set (Site 2))).Reachable ![1, 0] ![0, 1] := by
-- proof
  apply StatMech.Lattice.tnbp_singlePoint_nonvacuous

/--
[tnbp_reachesExterior_insert_of_ringClear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNonBridgeProve.lean)
-/
@[path]
private lemma tnbp_reachesExterior_insert_of_ringClear_eq
  {B : Set (Site 2)}
  {R : ℕ}
  {c : Site 2}
-- given
  (hbase : arcxc_ReachesExterior B R)
  (hc : c ∈ box 2 R)
  (hclear : tnbp_RingClear c B) :
-- imply
  arcxc_ReachesExterior (insert c B) R := by
-- proof
  apply StatMech.Lattice.tnbp_reachesExterior_insert_of_ringClear hbase hc hclear


-- created on 2026-10-23
