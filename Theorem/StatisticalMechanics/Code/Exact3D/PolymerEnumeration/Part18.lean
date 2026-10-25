/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part21


namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace BoundedPolymerCase

@[simp] theorem coordinatePermutationEquivalent_refl
    {d R maxDegree maxRange : ℕ}
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    coordinatePermutationEquivalent c c := by
  refine ⟨rfl, rfl, ⟨Equiv.refl (Fin d), ?_⟩⟩
  simp

theorem coordinatePermutationEquivalent_symm {d R maxDegree maxRange : ℕ}
    {c c' : BoundedPolymerCase d R maxDegree maxRange}
    (h : coordinatePermutationEquivalent c c') :
    coordinatePermutationEquivalent c' c := by
  rcases h with ⟨hdegree, hrange, σ, hsupport⟩
  refine ⟨hdegree.symm, hrange.symm, ⟨σ.symm, ?_⟩⟩
  have hpermuted :
      c'.toPolymerSupport.permuteCoordinates σ.symm =
        c.toPolymerSupport := by
    rw [hsupport, PolymerSupport.permuteCoordinates_trans]
    simp
  exact hpermuted.symm

theorem coordinatePermutationEquivalent_trans {d R maxDegree maxRange : ℕ}
    {c₁ c₂ c₃ : BoundedPolymerCase d R maxDegree maxRange}
    (h₁₂ : coordinatePermutationEquivalent c₁ c₂)
    (h₂₃ : coordinatePermutationEquivalent c₂ c₃) :
    coordinatePermutationEquivalent c₁ c₃ := by
  rcases h₁₂ with ⟨hdegree₁₂, hrange₁₂, σ, hsupport₁₂⟩
  rcases h₂₃ with ⟨hdegree₂₃, hrange₂₃, τ, hsupport₂₃⟩
  refine ⟨hdegree₁₂.trans hdegree₂₃, hrange₁₂.trans hrange₂₃,
    ⟨σ.trans τ, ?_⟩⟩
  calc
    c₃.toPolymerSupport = c₂.toPolymerSupport.permuteCoordinates τ := hsupport₂₃
    _ = (c₁.toPolymerSupport.permuteCoordinates σ).permuteCoordinates τ := by
      rw [hsupport₁₂]
    _ = c₁.toPolymerSupport.permuteCoordinates (σ.trans τ) := by
      rw [PolymerSupport.permuteCoordinates_trans]


end BoundedPolymerCase
end
end Exact3D
end StatMech
