/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarFaceGeometric.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeneral
import Def.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part4
open SimpleGraph Set


namespace StatMech.Lattice

attribute [instance] PlanarZ2Subgraph.finV PlanarZ2Subgraph.decV


theorem regionGraph_reachable_of_exterior (P : PlanarZ2Subgraph) (R : ℕ)
    (hR : ∀ v : P.V, P.emb v ∈ box 2 R) {f g : Site 2}
    (hf : f ∈ exterior 2 R) (hg : g ∈ exterior 2 R)
    (h : ((hypercubicLattice 2).induce (exterior 2 R)).Reachable ⟨f, hf⟩ ⟨g, hg⟩) :
    (regionGraph (imageGraph P)).Reachable f g := by
  have hmap := h.map (exteriorToRegionHom P R hR)
  simpa [exteriorToRegionHom] using hmap


theorem exists_infinite_region (P : PlanarZ2Subgraph) :
    ∃ C : (regionGraph (imageGraph P)).ConnectedComponent, C.supp.Infinite := by
  obtain ⟨R, hR⟩ := image_subset_box P
  set RG := regionGraph (imageGraph P) with hRG
  have hb_ext : beacon 2 R ∈ exterior 2 R := beacon_mem_exterior R (by omega)
  set C0 := RG.connectedComponentMk (beacon 2 R) with hC0
  refine ⟨C0, ?_⟩
  have hExtComp : ∀ x : Site 2, x ∈ exterior 2 R → RG.connectedComponentMk x = C0 := by
    intro x hx
    exact ConnectedComponent.sound
      (regionGraph_reachable_of_exterior P R hR hx hb_ext
        (box_exterior_connected R (by omega) x (beacon 2 R) hx hb_ext))
  have : Infinite ↥(exterior 2 R) := (exterior_infinite R (by omega)).to_subtype
  refine Set.infinite_of_injective_forall_mem
    (f := fun w : ↥(exterior 2 R) => (w : Site 2)) ?_ ?_
  · intro a b hab; exact Subtype.ext hab
  · intro w
    rw [ConnectedComponent.mem_supp_iff]
    exact hExtComp (w : Site 2) w.2


end StatMech.Lattice
