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
import Instance.StatisticalMechanics.Code.Lattice.TreeNoSepEuler
open SimpleGraph Set

set_option linter.unusedSectionVars false


namespace StatMech

namespace Lattice

variable {V : Type*} [Finite V] [DecidableEq V]


theorem tnse_site_ne_of_col {x y x' y' : ℤ} (h : x ≠ x') : (![x, y] : Site 2) ≠ ![x', y'] := by
  intro he; exact h (by have := congrFun he 0; simpa using this)


theorem tnse_site_ne_of_row {x y x' y' : ℤ} (h : y ≠ y') : (![x, y] : Site 2) ≠ ![x', y'] := by
  intro he; exact h (by have := congrFun he 1; simpa using this)


theorem tnse_horizEdge_nonbridge {R : ℕ} {x y : ℤ}
    (hx : x.natAbs ≤ R) (hx1 : (x + 1).natAbs ≤ R) (hy : y.natAbs ≤ R) (hy1 : (y + 1).natAbs ≤ R) :
    tnse_IsNonBridgeEdge (boxInduce R)
      s((⟨![x, y], mem_box2 hx hy⟩ : ↥(box 2 R)),
        (⟨![x + 1, y], mem_box2 hx1 hy⟩ : ↥(box 2 R))) := by
  refine tnse_grid_edge_nonbridge_of_detour (boxInduce R)
    (a' := ⟨![x, y + 1], mem_box2 hx hy1⟩) (b' := ⟨![x + 1, y + 1], mem_box2 hx1 hy1⟩)
    (by rw [SimpleGraph.mem_edgeSet]; exact boxInduce_adj _ _ (hadj_step x y))
    (boxInduce_adj _ _ (vadj_step x y))
    (boxInduce_adj _ _ (hadj_step x (y + 1)))
    (boxInduce_adj _ _ (vadj_step (x + 1) y).symm) ?_ ?_ ?_
  · 
    rw [Ne, Sym2.eq_iff, not_or]
    refine ⟨fun ⟨_, h2⟩ => ?_, fun ⟨h1, _⟩ => ?_⟩
    · exact tnse_site_ne_of_row (by omega) (Subtype.ext_iff.mp h2)
    · exact tnse_site_ne_of_col (by omega) (Subtype.ext_iff.mp h1)
  · 
    rw [Ne, Sym2.eq_iff, not_or]
    refine ⟨fun ⟨h1, _⟩ => ?_, fun ⟨h1, _⟩ => ?_⟩
    · exact tnse_site_ne_of_row (by omega) (Subtype.ext_iff.mp h1)
    · exact tnse_site_ne_of_row (by omega) (Subtype.ext_iff.mp h1)
  · 
    rw [Ne, Sym2.eq_iff, not_or]
    refine ⟨fun ⟨h1, _⟩ => ?_, fun ⟨_, h2⟩ => ?_⟩
    · exact tnse_site_ne_of_col (by omega) (Subtype.ext_iff.mp h1)
    · exact tnse_site_ne_of_col (by omega) (Subtype.ext_iff.mp h2)


theorem tnse_deleteList_adj_of_notMem {A : SimpleGraph V} {c d : V} (h : A.Adj c d) :
    ∀ {L : List (Sym2 V)}, s(c, d) ∉ L → (tnse_deleteList A L).Adj c d := by
  intro L
  induction L with
  | nil => intro _; simpa using h
  | cons e L ih =>
    intro hmem
    rw [List.mem_cons, not_or] at hmem
    rw [tnse_deleteList_cons, SimpleGraph.deleteEdges_adj]
    exact ⟨ih hmem.2, by simpa [eq_comm] using hmem.1⟩


theorem tnse_nonbridge_of_detour_notMem {A : SimpleGraph V} {a b a' b' : V} {L : List (Sym2 V)}
    (hab : s(a, b) ∈ (tnse_deleteList A L).edgeSet)
    (h1 : A.Adj a a') (h2 : A.Adj a' b') (h3 : A.Adj b' b)
    (hne1 : s(a, a') ≠ s(a, b)) (hne2 : s(a', b') ≠ s(a, b)) (hne3 : s(b', b) ≠ s(a, b))
    (hL1 : s(a, a') ∉ L) (hL2 : s(a', b') ∉ L) (hL3 : s(b', b) ∉ L) :
    tnse_IsNonBridgeEdge (tnse_deleteList A L) s(a, b) :=
  tnse_grid_edge_nonbridge_of_detour (tnse_deleteList A L) hab
    (tnse_deleteList_adj_of_notMem h1 hL1)
    (tnse_deleteList_adj_of_notMem h2 hL2)
    (tnse_deleteList_adj_of_notMem h3 hL3) hne1 hne2 hne3


end Lattice
end StatMech
