/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneUniqueness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.FK.FiniteEnergy.Part4
import Def.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness
open MeasureTheory
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


@[simp] lemma removeSite_apply_of_mem {x : Site d} {e : Sym2 (Site d)} (h : x ∈ e)
    (ω : ConfigSpace (Sym2 (Site d))) : removeSite x ω e = false := by
  simp [removeSite, h]

@[simp] lemma removeSite_apply_of_notMem {x : Site d} {e : Sym2 (Site d)} (h : x ∉ e)
    (ω : ConfigSpace (Sym2 (Site d))) : removeSite x ω e = ω e := by
  simp [removeSite, h]


theorem measurable_removeSite (x : Site d) :
    Measurable (fun ω : ConfigSpace (Sym2 (Site d)) => removeSite x ω) := by
  apply measurable_pi_lambda
  intro e
  unfold removeSite
  by_cases h : x ∈ e
  · simp [h]
  · simp only [h, if_false]; exact measurable_pi_apply e


theorem removeSite_shift (g : Multiplicative (Site d)) (x : Site d)
    (ω : ConfigSpace (Sym2 (Site d))) :
    removeSite (g • x) (shift g ω) = shift g (removeSite x ω) := by
  funext e
  unfold removeSite
  rw [shift_apply, shift_apply]
  have hmem : (g • x ∈ e) ↔ (x ∈ g⁻¹ • e) := by
    constructor
    · intro h
      have : g⁻¹ • (g • x) ∈ g⁻¹ • e := Sym2.mem_map.mpr ⟨g • x, h, rfl⟩
      rwa [inv_smul_smul] at this
    · intro h
      have : g • x ∈ g • (g⁻¹ • e) := Sym2.mem_map.mpr ⟨x, h, rfl⟩
      rwa [smul_inv_smul] at this
  by_cases h : g • x ∈ e
  · rw [if_pos h, if_pos (hmem.mp h)]
  · rw [if_neg h, if_neg (fun hc => h (hmem.mpr hc))]


end Percolation
end StatMech
