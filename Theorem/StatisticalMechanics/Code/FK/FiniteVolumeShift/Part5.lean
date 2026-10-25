/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteVolumeShift.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.TranslationInvariance.Part5
import Instance.StatisticalMechanics.Code.FK.FiniteVolumeShift.Part3
open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open StatMech.Lattice

variable {d : ℕ}


theorem fvs_transEquiv_adj (d m : ℕ) (v : Site d) (x y : boxVerts d m) :
    (boxGraph d m).Adj x y
      ↔ (fvs_transBoxGraph d m v).Adj (fvs_transEquiv d m v x) (fvs_transEquiv d m v y) := by
  rw [boxGraph, fvs_transBoxGraph, SimpleGraph.comap_adj, SimpleGraph.comap_adj]
  show (hypercubicLattice d).Adj x.val y.val
    ↔ (hypercubicLattice d).Adj ((x : Site d) + v) ((y : Site d) + v)
  simp only [hypercubicLattice_adj]
  refine ⟨fun h => ?_, fun h => ?_⟩ <;>
    rw [← h] <;> refine Finset.sum_congr rfl (fun i _ => ?_) <;> simp [Pi.add_apply]


theorem fvs_transEquiv_boundary (d m : ℕ) (v : Site d) (x : boxVerts d m) :
    boxBoundary d m x ↔ fvs_transBoxBoundary d m v (fvs_transEquiv d m v x) := by
  unfold boxBoundary fvs_transBoxBoundary
  show (x : Site d) ∈ vertexBoundary d m ↔ ((x : Site d) + v - v) ∈ vertexBoundary d m
  rw [add_sub_cancel_right]


theorem fvs_box_translation_edgeMarg (d m : ℕ) (v : Site d) (eb : Sym2 (boxVerts d m))
    {p q : ℝ} :
    edgeMargProb (wiredFkProb (fvs_transBoxGraph d m v) (fvs_transBoxBoundary d m v) p q)
          (Sym2.map (fvs_transEquiv d m v) eb)
        = edgeMargProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p q) eb
      ∧ edgeMargProb (fkProb (fvs_transBoxGraph d m v) p q) (Sym2.map (fvs_transEquiv d m v) eb)
        = edgeMargProb (fkProb (boxGraph d m) p q) eb :=
  fvs_finiteVolume_shift_invariant (boxGraph d m) (fvs_transBoxGraph d m v)
    (boxBoundary d m) (fvs_transBoxBoundary d m v) (fvs_transEquiv d m v)
    (fvs_transEquiv_adj d m v) (fvs_transEquiv_boundary d m v) p q eb


theorem fvs_transBox_ne_box (d m : ℕ) (hd : 0 < d) :
    ∃ (v y : Site d), y ∈ fvs_transBox d m v ∧ y ∉ box d m := by
  refine ⟨fun i => if i = ⟨0, hd⟩ then 1 else 0,
          fun i => if i = ⟨0, hd⟩ then (m : ℤ) + 1 else 0, ?_, ?_⟩
  · show (fun i => (if i = ⟨0, hd⟩ then (m : ℤ) + 1 else 0)
        - (if i = ⟨0, hd⟩ then (1 : ℤ) else 0)) ∈ box d m
    intro i
    by_cases hi : i = ⟨0, hd⟩
    · simp only [hi, if_true]
      rw [show ((m : ℤ) + 1 - 1) = (m : ℤ) by ring, Int.natAbs_natCast]
    · simp [hi]
  · intro h
    have hi := h ⟨0, hd⟩
    simp only [if_true] at hi
    rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, Int.natAbs_natCast] at hi
    omega

end FK
end StatMech
