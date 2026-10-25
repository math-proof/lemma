/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


theorem reachable_of_only_two_odd_degree
    {W : Type*} [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (l r : W)
    (hl : Odd (G.degree l))
    (hodd : ∀ v, Odd (G.degree v) → v = l ∨ v = r) :
    G.Reachable l r := by
  classical
  let C := G.connectedComponentMk l
  let S := C.supp
  let H := G.induce S
  have hlS : l ∈ S := by
    exact (C.mem_supp_iff l).2 (by simp [C])
  let lS : S := ⟨l, hlS⟩
  have hdegree (v : S) : H.degree v = G.degree (v : W) := by
    have hneighbor : (H.neighborFinset v).image Subtype.val =
        G.neighborFinset (v : W) := by
      ext w
      simp only [Finset.mem_image, mem_neighborFinset]
      constructor
      · rintro ⟨u, huv, rfl⟩
        exact induce_adj.mp huv
      · intro hvw
        have hwS : w ∈ S := by
          apply (C.mem_supp_iff w).2
          have hvC : G.connectedComponentMk (v : W) = C :=
            (C.mem_supp_iff (v : W)).mp v.2
          exact (ConnectedComponent.sound hvw.reachable).symm.trans hvC
        exact ⟨⟨w, hwS⟩, induce_adj.mpr hvw, rfl⟩
    rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree,
      ← hneighbor]
    exact (Finset.card_image_of_injective _ Subtype.val_injective).symm
  have hlOdd : Odd (H.degree lS) := by
    rw [hdegree]
    exact hl
  obtain ⟨w, hwl, hwOdd⟩ :=
    H.exists_ne_odd_degree_of_exists_odd_degree lS hlOdd
  have hwOddG : Odd (G.degree (w : W)) := by
    rw [← hdegree]
    exact hwOdd
  rcases hodd (w : W) hwOddG with hw | hw
  · exact (hwl (Subtype.ext hw)).elim
  · apply ConnectedComponent.exact
    change G.connectedComponentMk l = G.connectedComponentMk r
    have hwr : r ∈ C.supp := by simpa [hw] using w.2
    simpa [C] using ((C.mem_supp_iff r).mp hwr).symm


end StatMech.FK.PeriodicPlanar
