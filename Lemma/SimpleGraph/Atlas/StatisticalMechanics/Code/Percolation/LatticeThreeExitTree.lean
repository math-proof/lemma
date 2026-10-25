import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Percolation.LatticeThreeExitTree.Part2
open Set SimpleGraph Finset StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[threeExitTip_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeThreeExitTree.lean)
-/
@[path]
private lemma threeExitTip_injective_eq
  {d n : ℕ} :
-- imply
  Function.Injective (threeExitTip (d := d) (n := n)) := by
-- proof
  apply StatMech.Percolation.threeExitTip_injective

/--
[threeExitTip_degree_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeThreeExitTree.lean)
-/
@[path]
private lemma threeExitTip_degree_one_eq
  {d n : ℕ}
  {inside : Fin 3 → Site d}
  {i : Fin 3}
-- given
  (hinside : ∀ i, inside i ∈ box d n) :
-- imply
  (threeExitGraph (n := n) inside).degree (threeExitTip i) = 1 := by
-- proof
  apply StatMech.Percolation.threeExitTip_degree_one inside hinside i

/--
[threeExitGraph_core_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeThreeExitTree.lean)
-/
@[path]
private lemma threeExitGraph_core_reachable_eq
  {d n : ℕ}
  {inside : Fin 3 → Site d}
  {x y : ↑(boxFinsetBK d n)} :
-- imply
  (threeExitGraph inside).Reachable (Sum.inl x) (Sum.inl y) := by
-- proof
  apply StatMech.Percolation.threeExitGraph_core_reachable inside

/--
[threeExitGraph_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeThreeExitTree.lean)
-/
@[path]
private lemma threeExitGraph_connected_eq
  {d n : ℕ}
  {inside : Fin 3 → Site d}
-- given
  (hinside : ∀ i, inside i ∈ box d n) :
-- imply
  (threeExitGraph (n := n) inside).Connected := by
-- proof
  apply StatMech.Percolation.threeExitGraph_connected inside hinside

/--
[threeExitSite_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeThreeExitTree.lean)
-/
@[path]
private lemma threeExitSite_injective_eq
  {d n : ℕ}
  {outside : Fin 3 → Site d}
-- given
  (hout : ∀ i, outside i ∉ box d n)
  (houtinj : Function.Injective outside) :
-- imply
  Function.Injective (threeExitSite (d := d) (n := n) outside) := by
-- proof
  apply StatMech.Percolation.threeExitSite_injective outside hout houtinj

/--
[threeExitGraph_maps_to_lattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeThreeExitTree.lean)
-/
@[path]
private lemma threeExitGraph_maps_to_lattice_eq
  {d n : ℕ}
  {inside outside : Fin 3 → Site d}
  {a b : ThreeExitVertex d n}
-- given
  (hexit : ∀ i, (hypercubicLattice d).Adj (inside i) (outside i))
  (hab : (threeExitGraph inside).Adj a b) :
-- imply
  (hypercubicLattice d).Adj (threeExitSite outside a) (threeExitSite outside b) := by
-- proof
  apply StatMech.Percolation.threeExitGraph_maps_to_lattice inside outside hexit hab

/--
[lattice_three_exit_tree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeThreeExitTree.lean)
-/
@[path]
private lemma lattice_three_exit_tree_eq
  {d n : ℕ}
  {inside outside : Fin 3 → Site d}
-- given
  (hinside : ∀ i, inside i ∈ box d n)
  (hout : ∀ i, outside i ∉ box d n)
  (houtinj : Function.Injective outside)
  (hexit : ∀ i, (hypercubicLattice d).Adj (inside i) (outside i)) :
-- imply
  ∃ (C : Set (ThreeExitVertex d n)) (T : SimpleGraph C) (_ : DecidableRel T.Adj) (hub : C) (stem leaf : Fin 3 → C), T.IsTree ∧ Function.Injective (fun z : C => threeExitSite outside z.1) ∧ (∀ a b, T.Adj a b → (threeExitGraph inside).Adj a.1 b.1) ∧ (∀ a b, T.Adj a b → (hypercubicLattice d).Adj (threeExitSite outside a.1) (threeExitSite outside b.1)) ∧ Function.Injective stem ∧ (∀ i, T.Adj hub (stem i)) ∧ Function.Injective leaf ∧ (∀ i, ∃ j, threeExitSite outside (leaf i).1 = outside j) ∧ (∀ j, ∃ i, (leaf i).1 = threeExitTip j) ∧ (∀ i, (T.deleteIncidenceSet hub).Reachable (stem i) (leaf i)) ∧ (∀ i, T.Reachable hub (leaf i)) ∧ (∀ i j, i ≠ j → ¬ (T.deleteIncidenceSet hub).Reachable (leaf i) (leaf j)) := by
-- proof
  apply StatMech.Percolation.lattice_three_exit_tree inside outside hinside hout houtinj hexit


-- created on 2026-10-23
