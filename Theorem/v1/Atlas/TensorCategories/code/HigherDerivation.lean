/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HigherDerivation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finite
import Structure.v1.Atlas.TensorCategories.code.HigherDerivation
set_option maxHeartbeats 800000

universe v u w


namespace TensorCategories

section Ext1UnitVanishing

/-- Main vanishing theorem (used in the proof of Theorem 1.27.4): on a finite-dimensional
algebra in characteristic zero, the first higher derivation `χ 1` of any system is zero. -/
theorem higher_derivation_vanishes [CharZero k] [FiniteDimensional k A] :
    hds.χ 1 = 0 := by
  by_contra hne
  have hne' : ∃ a₀ : A, hds.χ 1 a₀ ≠ 0 := by
    by_contra h; push Not at h; exact hne (LinearMap.ext h)
  obtain ⟨a₀, ha₀⟩ := hne'
  set a := a₀ - algebraMap k A (ε a₀)
  have ha_ker : ε a = 0 := by
    show ε (a₀ - algebraMap k A (ε a₀)) = 0
    rw [map_sub, AlgHom.commutes]; exact sub_self _
  have hχ₁a : hds.χ 1 a ≠ 0 := by
    show hds.χ 1 (a₀ - algebraMap k A (ε a₀)) ≠ 0
    rw [map_sub, hds.χ_one_algebraMap, sub_zero]; exact ha₀

  have hli := hds.powers_linearIndependent ha_ker hχ₁a

  set N := Module.finrank k A + 1
  have hli_fin : LinearIndependent k ((fun n : ℕ => a ^ n) ∘ (Fin.val : Fin N → ℕ)) :=
    hli.comp Fin.val Fin.val_injective

  have hcard := hli_fin.fintype_card_le_finrank
  rw [Fintype.card_fin] at hcard
  omega

end Ext1UnitVanishing
end TensorCategories
