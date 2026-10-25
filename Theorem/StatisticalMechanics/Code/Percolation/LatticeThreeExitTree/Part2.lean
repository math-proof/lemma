/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeThreeExitTree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
import Theorem.StatisticalMechanics.Code.Percolation.ThreePendantTree
import Def.StatisticalMechanics.Code.Percolation.LatticeThreeExitTree.Part3
open Set SimpleGraph Finset
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech.Percolation

variable {d n : ℕ}


theorem threeExitSite_injective (outside : Fin 3 → Site d)
    (hout : ∀ i, outside i ∉ box d n) (houtinj : Function.Injective outside) :
    Function.Injective (threeExitSite (d := d) (n := n) outside) := by
  intro a b h
  rcases a with a | i <;> rcases b with b | j
  · exact congrArg Sum.inl (Subtype.ext h)
  · exfalso
    change a.1 = outside j at h
    exact hout j (h ▸ (by
      simpa only [boxFinsetBK, Set.Finite.mem_toFinset] using a.2))
  · exfalso
    change outside i = b.1 at h
    exact hout i (h.symm ▸ (by
      simpa only [boxFinsetBK, Set.Finite.mem_toFinset] using b.2))
  · exact congrArg Sum.inr (houtinj h)

theorem threeExitGraph_maps_to_lattice (inside outside : Fin 3 → Site d)
    (hexit : ∀ i, (hypercubicLattice d).Adj (inside i) (outside i))
    {a b : ThreeExitVertex d n} (hab : (threeExitGraph inside).Adj a b) :
    (hypercubicLattice d).Adj (threeExitSite outside a) (threeExitSite outside b) := by
  rcases a with a | i <;> rcases b with b | j
  · exact hab
  · simpa [threeExitGraph, threeExitSite] using hab ▸ hexit j
  · simpa [threeExitGraph, threeExitSite] using hab ▸ (hexit i).symm
  · simp [threeExitGraph] at hab


theorem lattice_three_exit_tree (inside outside : Fin 3 → Site d)
    (hinside : ∀ i, inside i ∈ box d n)
    (hout : ∀ i, outside i ∉ box d n)
    (houtinj : Function.Injective outside)
    (hexit : ∀ i, (hypercubicLattice d).Adj (inside i) (outside i)) :
    ∃ (C : Set (ThreeExitVertex d n)) (T : SimpleGraph C)
      (_ : DecidableRel T.Adj) (hub : C) (stem leaf : Fin 3 → C),
      T.IsTree ∧
      Function.Injective (fun z : C => threeExitSite outside z.1) ∧
      (∀ a b, T.Adj a b → (threeExitGraph inside).Adj a.1 b.1) ∧
      (∀ a b, T.Adj a b →
        (hypercubicLattice d).Adj
          (threeExitSite outside a.1) (threeExitSite outside b.1)) ∧
      Function.Injective stem ∧
      (∀ i, T.Adj hub (stem i)) ∧
      Function.Injective leaf ∧
      (∀ i, ∃ j, threeExitSite outside (leaf i).1 = outside j) ∧
      (∀ j, ∃ i, (leaf i).1 = threeExitTip j) ∧
      (∀ i, (T.deleteIncidenceSet hub).Reachable (stem i) (leaf i)) ∧
      (∀ i, T.Reachable hub (leaf i)) ∧
      (∀ i j, i ≠ j →
        ¬ (T.deleteIncidenceSet hub).Reachable (leaf i) (leaf j)) := by
  classical
  let G := threeExitGraph (n := n) inside
  have hconn : G.Connected := threeExitGraph_connected inside hinside
  have hpdeg : ∀ i, G.degree (threeExitTip i) = 1 :=
    threeExitTip_degree_one inside hinside
  obtain ⟨C, T, hTdec, hub, stem, leaf, hTree, hTG, hsteminj,
      hstemadj, hleafinj, hleafTip, hstemleaf, hreach, hcut⟩ :=
    three_pendant_vertices_have_tripod G hconn threeExitTip
      threeExitTip_injective hpdeg
  choose sigma hsigma using hleafTip
  have hsigma_inj : Function.Injective sigma := by
    intro i j hij
    apply hleafinj
    apply Subtype.ext
    rw [hsigma i, hsigma j, hij]
  have hsigma_surj : Function.Surjective sigma :=
    Finite.injective_iff_surjective.mp hsigma_inj
  have htip_surj : ∀ j, ∃ i, (leaf i).1 = threeExitTip j := by
    intro j
    obtain ⟨i, hi⟩ := hsigma_surj j
    exact ⟨i, by rw [hsigma i, hi]⟩
  refine ⟨C, T, hTdec, hub, stem, leaf, hTree, ?_, hTG, ?_, hsteminj,
    hstemadj, hleafinj, ?_, htip_surj, hstemleaf, hreach, hcut⟩
  · exact (threeExitSite_injective outside hout houtinj).comp Subtype.val_injective
  · intro a b hab
    exact threeExitGraph_maps_to_lattice inside outside hexit (hTG a b hab)
  · intro i
    exact ⟨sigma i, by rw [hsigma i]; rfl⟩

end StatMech.Percolation
