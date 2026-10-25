/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanOuterFaceUnique.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
import Def.StatisticalMechanics.Code.Lattice.JordanOuterFaceUnique.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem exterior_in_outerRegion (P : PlanarZ2Subgraph) {x : Site 2}
    (hx : x ∈ exterior 2 (outerBoxRadius P)) :
    (regionGraph (imageGraph P)).connectedComponentMk x = outerRegion P := by
  set R := outerBoxRadius P with hR
  have hRbox := outerBoxRadius_spec P
  have hb_ext : beacon 2 R ∈ exterior 2 R := beacon_mem_exterior R (by omega)
  exact ConnectedComponent.sound
    (regionGraph_reachable_of_exterior P R hRbox hx hb_ext
      (box_exterior_connected R (by omega) x (beacon 2 R) hx hb_ext))


theorem outerRegion_infinite (P : PlanarZ2Subgraph) :
    (outerRegion P).supp.Infinite := by
  set R := outerBoxRadius P with hR
  have : Infinite ↥(exterior 2 R) := (exterior_infinite R (by omega)).to_subtype
  refine Set.infinite_of_injective_forall_mem
    (f := fun w : ↥(exterior 2 R) => (w : Site 2)) ?_ ?_
  · intro a b hab; exact Subtype.ext hab
  · intro w
    rw [ConnectedComponent.mem_supp_iff]
    exact exterior_in_outerRegion P w.2


theorem infiniteComponent_meets_exterior (P : PlanarZ2Subgraph)
    {C : (regionGraph (imageGraph P)).ConnectedComponent} (hC : C.supp.Infinite) :
    ∃ x ∈ C.supp, x ∈ exterior 2 (outerBoxRadius P) := by
  set R := outerBoxRadius P with hR
  by_contra hcon
  push Not at hcon
  have hsubbox : C.supp ⊆ box 2 R := by
    intro v hv
    have hvnotext : v ∉ exterior 2 R := hcon v hv
    rw [exterior_eq_compl_box, Set.mem_compl_iff, not_not] at hvnotext
    exact hvnotext
  exact hC ((box_finite 2 R).subset hsubbox)


theorem regionGraph_unique_infinite_component (P : PlanarZ2Subgraph) :
    ∃! C : (regionGraph (imageGraph P)).ConnectedComponent, C.supp.Infinite := by
  refine ⟨outerRegion P, outerRegion_infinite P, ?_⟩
  intro C hCinf
  obtain ⟨x, hx_supp, hx_ext⟩ := infiniteComponent_meets_exterior P hCinf
  have h1 : (regionGraph (imageGraph P)).connectedComponentMk x = C :=
    (C.mem_supp_iff x).mp hx_supp
  have h2 : (regionGraph (imageGraph P)).connectedComponentMk x = outerRegion P :=
    exterior_in_outerRegion P hx_ext
  rw [← h1, h2]


theorem outerRegion_eq_of_infinite (P : PlanarZ2Subgraph)
    {C : (regionGraph (imageGraph P)).ConnectedComponent} (hC : C.supp.Infinite) :
    C = outerRegion P :=
  ((regionGraph_unique_infinite_component P).unique hC (outerRegion_infinite P))


theorem boundedRegion_iff_ne_outer (P : PlanarZ2Subgraph)
    (C : (regionGraph (imageGraph P)).ConnectedComponent) :
    C.supp.Finite ↔ C ≠ outerRegion P := by
  constructor
  · intro hfin hcon
    rw [hcon] at hfin
    exact (outerRegion_infinite P) hfin
  · intro hne
    by_contra hinf
    rw [Set.not_finite] at hinf
    exact hne (outerRegion_eq_of_infinite P hinf)


end Lattice
end StatMech
