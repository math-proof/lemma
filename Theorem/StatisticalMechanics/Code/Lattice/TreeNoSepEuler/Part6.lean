/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNoSepEuler.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.EulerComponentCount.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces.Part3
import Def.StatisticalMechanics.Code.Lattice.TreeNoSepEuler.Part4
open SimpleGraph Set

set_option linter.unusedSectionVars false


namespace StatMech

namespace Lattice

variable {V : Type*} [Finite V] [DecidableEq V]


theorem tnse_allNonBridge_of_treeFreeDetour {A : SimpleGraph V} :
    ∀ {L : List (Sym2 V)}, L.Nodup → (∀ e ∈ L, tnse_HasTreeFreeDetour A L e) →
      tnse_AllNonBridge A L := by
  intro L
  induction L with
  | nil => intro _ _; trivial
  | cons e L' ih =>
    intro hnodup hdet
    rw [List.nodup_cons] at hnodup
    obtain ⟨henotin, hnodup'⟩ := hnodup
    refine tnse_allNonBridge_cons ?_ ?_
    · 
      obtain ⟨a, b, a', b', rfl, hab, h1, h2, h3, hne1, hne2, hne3, hL1, hL2, hL3⟩ :=
        hdet e List.mem_cons_self
      
      have hL1' : s(a, a') ∉ L' := fun h => hL1 (List.mem_cons_of_mem _ h)
      have hL2' : s(a', b') ∉ L' := fun h => hL2 (List.mem_cons_of_mem _ h)
      have hL3' : s(b', b) ∉ L' := fun h => hL3 (List.mem_cons_of_mem _ h)
      
      have hadjab : A.Adj a b := by rwa [SimpleGraph.mem_edgeSet] at hab
      have hsurv : s(a, b) ∈ (tnse_deleteList A L').edgeSet := by
        rw [SimpleGraph.mem_edgeSet]
        exact tnse_deleteList_adj_of_notMem hadjab henotin
      exact tnse_nonbridge_of_detour_notMem hsurv h1 h2 h3 hne1 hne2 hne3 hL1' hL2' hL3'
    · 
      refine ih hnodup' (fun f hf => ?_)
      obtain ⟨a, b, a', b', hfe, hab, h1, h2, h3, hne1, hne2, hne3, hL1, hL2, hL3⟩ :=
        hdet f (List.mem_cons_of_mem _ hf)
      exact ⟨a, b, a', b', hfe, hab, h1, h2, h3, hne1, hne2, hne3,
        fun h => hL1 (List.mem_cons_of_mem _ h),
        fun h => hL2 (List.mem_cons_of_mem _ h),
        fun h => hL3 (List.mem_cons_of_mem _ h)⟩


theorem tnse_box_minus_treeFreeDetour_connected {R : ℕ} {L : List (Sym2 ↥(box 2 R))}
    (hnodup : L.Nodup) (hdet : ∀ e ∈ L, tnse_HasTreeFreeDetour (boxInduce R) L e) :
    (tnse_deleteList (boxInduce R) L).Connected :=
  tnse_connected_deleteList_of_allNonBridge (boxInduce R) (boxInduce_connected R)
    (tnse_allNonBridge_of_treeFreeDetour hnodup hdet)


theorem tnse_box_minus_tree_connected {R : ℕ} {L : List (Sym2 ↥(box 2 R))}
    (hnb : tnse_AllNonBridge (boxInduce R) L) :
    (tnse_deleteList (boxInduce R) L).Connected :=
  tnse_connected_deleteList_of_allNonBridge (boxInduce R) (boxInduce_connected R) hnb


theorem tnse_box_minus_nil_connected (R : ℕ) :
    (tnse_deleteList (boxInduce R) []).Connected := by
  simpa using boxInduce_connected R


theorem tnse_box_minus_singleHorizEdge_connected {R : ℕ} {x y : ℤ}
    (hx : x.natAbs ≤ R) (hx1 : (x + 1).natAbs ≤ R) (hy : y.natAbs ≤ R) (hy1 : (y + 1).natAbs ≤ R) :
    (tnse_deleteList (boxInduce R)
      [s((⟨![x, y], mem_box2 hx hy⟩ : ↥(box 2 R)),
         (⟨![x + 1, y], mem_box2 hx1 hy⟩ : ↥(box 2 R)))]).Connected := by
  apply tnse_box_minus_tree_connected
  refine tnse_allNonBridge_cons ?_ (tnse_allNonBridge_nil _)
  simpa using tnse_horizEdge_nonbridge hx hx1 hy hy1


theorem tnse_singleHorizEdge_treeFreeDetour {R : ℕ} {x y : ℤ}
    (hx : x.natAbs ≤ R) (hx1 : (x + 1).natAbs ≤ R) (hy : y.natAbs ≤ R) (hy1 : (y + 1).natAbs ≤ R) :
    ∀ e ∈ [s((⟨![x, y], mem_box2 hx hy⟩ : ↥(box 2 R)),
             (⟨![x + 1, y], mem_box2 hx1 hy⟩ : ↥(box 2 R)))],
      tnse_HasTreeFreeDetour (boxInduce R)
        [s((⟨![x, y], mem_box2 hx hy⟩ : ↥(box 2 R)),
           (⟨![x + 1, y], mem_box2 hx1 hy⟩ : ↥(box 2 R)))] e := by
  intro e he
  rw [List.mem_singleton] at he
  subst he
  obtain ⟨a, b, _, hab, hr⟩ := tnse_horizEdge_nonbridge hx hx1 hy hy1
  
  refine ⟨⟨![x, y], mem_box2 hx hy⟩, ⟨![x + 1, y], mem_box2 hx1 hy⟩,
    ⟨![x, y + 1], mem_box2 hx hy1⟩, ⟨![x + 1, y + 1], mem_box2 hx1 hy1⟩, rfl,
    by rw [SimpleGraph.mem_edgeSet]; exact boxInduce_adj _ _ (hadj_step x y),
    boxInduce_adj _ _ (vadj_step x y), boxInduce_adj _ _ (hadj_step x (y + 1)),
    boxInduce_adj _ _ (vadj_step (x + 1) y).symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  
  · rw [Ne, Sym2.eq_iff, not_or]
    exact ⟨fun ⟨_, h2⟩ => tnse_site_ne_of_row (by omega) (Subtype.ext_iff.mp h2),
      fun ⟨h1, _⟩ => tnse_site_ne_of_col (by omega) (Subtype.ext_iff.mp h1)⟩
  · rw [Ne, Sym2.eq_iff, not_or]
    exact ⟨fun ⟨h1, _⟩ => tnse_site_ne_of_row (by omega) (Subtype.ext_iff.mp h1),
      fun ⟨h1, _⟩ => tnse_site_ne_of_row (by omega) (Subtype.ext_iff.mp h1)⟩
  · rw [Ne, Sym2.eq_iff, not_or]
    exact ⟨fun ⟨h1, _⟩ => tnse_site_ne_of_col (by omega) (Subtype.ext_iff.mp h1),
      fun ⟨_, h2⟩ => tnse_site_ne_of_col (by omega) (Subtype.ext_iff.mp h2)⟩
  
  · rw [List.mem_singleton, Sym2.eq_iff, not_or]
    exact ⟨fun ⟨_, h2⟩ => tnse_site_ne_of_row (by omega) (Subtype.ext_iff.mp h2),
      fun ⟨h1, _⟩ => tnse_site_ne_of_col (by omega) (Subtype.ext_iff.mp h1)⟩
  · rw [List.mem_singleton, Sym2.eq_iff, not_or]
    exact ⟨fun ⟨h1, _⟩ => tnse_site_ne_of_row (by omega) (Subtype.ext_iff.mp h1),
      fun ⟨h1, _⟩ => tnse_site_ne_of_row (by omega) (Subtype.ext_iff.mp h1)⟩
  · rw [List.mem_singleton, Sym2.eq_iff, not_or]
    exact ⟨fun ⟨h1, _⟩ => tnse_site_ne_of_col (by omega) (Subtype.ext_iff.mp h1),
      fun ⟨_, h2⟩ => tnse_site_ne_of_col (by omega) (Subtype.ext_iff.mp h2)⟩


theorem tnse_box_minus_singleHorizEdge_connected_orderFree {R : ℕ} {x y : ℤ}
    (hx : x.natAbs ≤ R) (hx1 : (x + 1).natAbs ≤ R) (hy : y.natAbs ≤ R) (hy1 : (y + 1).natAbs ≤ R) :
    (tnse_deleteList (boxInduce R)
      [s((⟨![x, y], mem_box2 hx hy⟩ : ↥(box 2 R)),
         (⟨![x + 1, y], mem_box2 hx1 hy⟩ : ↥(box 2 R)))]).Connected :=
  tnse_box_minus_treeFreeDetour_connected (List.nodup_singleton _)
    (tnse_singleHorizEdge_treeFreeDetour hx hx1 hy hy1)


theorem tnse_singleEdge_nonvacuous :
    (tnse_deleteList (boxInduce 2)
      [s((⟨![0, 0], mem_box2 (by decide) (by decide)⟩ : ↥(box 2 2)),
         (⟨![1, 0], mem_box2 (by decide) (by decide)⟩ : ↥(box 2 2)))]).Reachable
      (⟨![0, 0], mem_box2 (by decide) (by decide)⟩ : ↥(box 2 2))
      (⟨![1, 0], mem_box2 (by decide) (by decide)⟩ : ↥(box 2 2)) :=
  (tnse_box_minus_singleHorizEdge_connected (R := 2) (x := 0) (y := 0)
    (by decide) (by decide) (by decide) (by decide)) _ _


end Lattice
end StatMech
