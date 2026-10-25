/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part24


namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace BoundedPolymerCase

@[simp] theorem coordinateReflectionEquivalent_refl
    {d R maxDegree maxRange : ℕ}
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    coordinateReflectionEquivalent c c := by
  refine ⟨rfl, rfl, ⟨fun _ : Fin d => false, ?_⟩⟩
  simp

theorem coordinateReflectionEquivalent_symm {d R maxDegree maxRange : ℕ}
    {c c' : BoundedPolymerCase d R maxDegree maxRange}
    (h : coordinateReflectionEquivalent c c') :
    coordinateReflectionEquivalent c' c := by
  rcases h with ⟨hdegree, hrange, ε, hsupport⟩
  refine ⟨hdegree.symm, hrange.symm, ⟨ε, ?_⟩⟩
  have hxor :
      (fun i : Fin d => Bool.xor (ε i) (ε i)) =
        (fun _ : Fin d => false) := by
    funext i
    cases ε i <;> rfl
  have hreflected :
      c'.toPolymerSupport.reflectCoordinates ε = c.toPolymerSupport := by
    rw [hsupport, PolymerSupport.reflectCoordinates_reflectCoordinates, hxor]
    simp
  exact hreflected.symm

theorem coordinateReflectionEquivalent_trans {d R maxDegree maxRange : ℕ}
    {c₁ c₂ c₃ : BoundedPolymerCase d R maxDegree maxRange}
    (h₁₂ : coordinateReflectionEquivalent c₁ c₂)
    (h₂₃ : coordinateReflectionEquivalent c₂ c₃) :
    coordinateReflectionEquivalent c₁ c₃ := by
  rcases h₁₂ with ⟨hdegree₁₂, hrange₁₂, ε, hsupport₁₂⟩
  rcases h₂₃ with ⟨hdegree₂₃, hrange₂₃, δ, hsupport₂₃⟩
  refine ⟨hdegree₁₂.trans hdegree₂₃, hrange₁₂.trans hrange₂₃,
    ⟨fun i => Bool.xor (ε i) (δ i), ?_⟩⟩
  calc
    c₃.toPolymerSupport = c₂.toPolymerSupport.reflectCoordinates δ := hsupport₂₃
    _ = (c₁.toPolymerSupport.reflectCoordinates ε).reflectCoordinates δ := by
      rw [hsupport₁₂]
    _ = c₁.toPolymerSupport.reflectCoordinates
        (fun i => Bool.xor (ε i) (δ i)) := by
      rw [PolymerSupport.reflectCoordinates_reflectCoordinates]


end BoundedPolymerCase
end
end Exact3D
end StatMech
