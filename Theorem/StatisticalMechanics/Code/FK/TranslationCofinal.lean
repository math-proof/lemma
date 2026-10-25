/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationCofinal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.TranslationInvariance.Part5
import Def.StatisticalMechanics.Code.FK.TranslationCofinal
open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK ConfigSpace

variable {d : ℕ}


@[simp] theorem fktc_translate_apply (v x : Site d) : fktc_translate v x = x + v := rfl


theorem fktc_translate_adj (v : Site d) (x y : Site d) :
    (hypercubicLattice d).Adj (fktc_translate v x) (fktc_translate v y)
      ↔ (hypercubicLattice d).Adj x y := by
  simp only [hypercubicLattice_adj, fktc_translate_apply]
  have hcoord : ∀ i : Fin d, ((x + v) i - (y + v) i).natAbs = (x i - y i).natAbs := by
    intro i
    have : (x + v) i - (y + v) i = x i - y i := by
      simp only [Pi.add_apply]; ring
    rw [this]
  rw [Finset.sum_congr rfl (fun i _ => hcoord i)]


theorem fktc_translate_not_box_mem (j : Fin d) :
    ¬ (∀ n x, fktc_translate (fun i => if i = j then (1:ℤ) else 0) x ∈ box d n
        ↔ x ∈ box d n) := by
  intro h
  have hbase : (fun _ : Fin d => (0:ℤ)) ∈ box d 0 := by
    intro i; simp
  have := (h 0 (fun _ => 0)).mpr hbase
  rw [mem_box] at this
  have hj := this j
  simp only [fktc_translate_apply, Pi.add_apply] at hj
  norm_num at hj


theorem fktc_point_and_translate_in_box (v x : Site d) :
    ∃ N, x ∈ box d N ∧ fktc_translate v x ∈ box d N := by
  refine ⟨Finset.univ.sup (fun i => (x i).natAbs ⊔ ((x + v) i).natAbs), ?_, ?_⟩
  · intro i
    refine le_trans le_sup_left
      (Finset.le_sup (f := fun i => (x i).natAbs ⊔ ((x + v) i).natAbs) (Finset.mem_univ i))
  · intro i
    show ((x + v) i).natAbs ≤ _
    refine le_trans le_sup_right
      (Finset.le_sup (f := fun i => (x i).natAbs ⊔ ((x + v) i).natAbs) (Finset.mem_univ i))


theorem fktc_edge_and_translate_in_box (v x y : Site d) :
    ∃ N, x ∈ box d N ∧ y ∈ box d N ∧
      fktc_translate v x ∈ box d N ∧ fktc_translate v y ∈ box d N := by
  refine ⟨Finset.univ.sup
      (fun i => (x i).natAbs ⊔ (y i).natAbs ⊔ ((x + v) i).natAbs ⊔ ((y + v) i).natAbs),
    ?_, ?_, ?_, ?_⟩
  · intro i
    refine le_trans ?_
      (Finset.le_sup
        (f := fun i => (x i).natAbs ⊔ (y i).natAbs ⊔ ((x + v) i).natAbs ⊔ ((y + v) i).natAbs)
        (Finset.mem_univ i))
    exact le_trans le_sup_left (le_trans le_sup_left le_sup_left)
  · intro i
    refine le_trans ?_
      (Finset.le_sup
        (f := fun i => (x i).natAbs ⊔ (y i).natAbs ⊔ ((x + v) i).natAbs ⊔ ((y + v) i).natAbs)
        (Finset.mem_univ i))
    exact le_trans le_sup_right (le_trans le_sup_left le_sup_left)
  · intro i
    show ((x + v) i).natAbs ≤ _
    refine le_trans ?_
      (Finset.le_sup
        (f := fun i => (x i).natAbs ⊔ (y i).natAbs ⊔ ((x + v) i).natAbs ⊔ ((y + v) i).natAbs)
        (Finset.mem_univ i))
    exact le_trans le_sup_right le_sup_left
  · intro i
    show ((y + v) i).natAbs ≤ _
    refine le_trans ?_
      (Finset.le_sup
        (f := fun i => (x i).natAbs ⊔ (y i).natAbs ⊔ ((x + v) i).natAbs ⊔ ((y + v) i).natAbs)
        (Finset.mem_univ i))
    exact le_sup_right


theorem fktc_translate_cofinal (v x y : Site d) :
    ∃ N, x ∈ box d N ∧ y ∈ box d N ∧
      fktc_translate v x ∈ box d N ∧ fktc_translate v y ∈ box d N :=
  fktc_edge_and_translate_in_box v x y


end FK
end StatMech
