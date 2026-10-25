/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/MengerCorridors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneAttachment.Part4
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem mco_mergeFree_of_reach (ω : ConfigSpace (Sym2 (Site d)))
    (a₁ a₂ a₃ x₁ x₂ x₃ : Site d)
    (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃)
    (hconn : Connected d (removeSite 0 ω) a₁ x₁ ∧ Connected d (removeSite 0 ω) a₂ x₂ ∧
      Connected d (removeSite 0 ω) a₃ x₃)
    (hinf : (cluster d (removeSite 0 ω) x₁).Infinite ∧
      (cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite)
    (hdist : cluster d (removeSite 0 ω) x₁ ≠ cluster d (removeSite 0 ω) x₂ ∧
      cluster d (removeSite 0 ω) x₁ ≠ cluster d (removeSite 0 ω) x₃ ∧
      cluster d (removeSite 0 ω) x₂ ≠ cluster d (removeSite 0 ω) x₃) :
    bka_MergeFree ω := by
  obtain ⟨ha1, ha2, ha3⟩ := hadj
  obtain ⟨hc1, hc2, hc3⟩ := hconn
  obtain ⟨hi1, hi2, hi3⟩ := hinf
  obtain ⟨hd12, hd13, hd23⟩ := hdist
  
  have e1 : cluster d (removeSite 0 ω) a₁ = cluster d (removeSite 0 ω) x₁ :=
    cluster_eq_of_connected hc1
  have e2 : cluster d (removeSite 0 ω) a₂ = cluster d (removeSite 0 ω) x₂ :=
    cluster_eq_of_connected hc2
  have e3 : cluster d (removeSite 0 ω) a₃ = cluster d (removeSite 0 ω) x₃ :=
    cluster_eq_of_connected hc3
  refine ⟨a₁, a₂, a₃, ⟨?_, ?_, ?_⟩, ⟨ha1, ha2, ha3⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro h; apply hd12; rw [← e1, ← e2, h]
  · intro h; apply hd13; rw [← e1, ← e3, h]
  · intro h; apply hd23; rw [← e2, ← e3, h]
  · rw [e1]; exact hi1
  · rw [e2]; exact hi2
  · rw [e3]; exact hi3
  · rw [e1, e2]; exact hd12
  · rw [e1, e3]; exact hd13
  · rw [e2, e3]; exact hd23


end Percolation
end StatMech
