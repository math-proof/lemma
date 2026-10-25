/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part18


namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace BoundedPolymerCase

@[simp] theorem translationEquivalent_refl {d R maxDegree maxRange : ℕ}
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    translationEquivalent c c := by
  refine ⟨rfl, rfl, ⟨0, ?_⟩⟩
  simp

theorem translationEquivalent_symm {d R maxDegree maxRange : ℕ}
    {c c' : BoundedPolymerCase d R maxDegree maxRange}
    (h : translationEquivalent c c') :
    translationEquivalent c' c := by
  rcases h with ⟨hdegree, hrange, v, hsupport⟩
  refine ⟨hdegree.symm, hrange.symm, ⟨-v, ?_⟩⟩
  have htranslated :
      c'.toPolymerSupport.translate (-v) = c.toPolymerSupport := by
    rw [hsupport, PolymerSupport.translate_translate]
    simp
  exact htranslated.symm

theorem translationEquivalent_trans {d R maxDegree maxRange : ℕ}
    {c₁ c₂ c₃ : BoundedPolymerCase d R maxDegree maxRange}
    (h₁₂ : translationEquivalent c₁ c₂)
    (h₂₃ : translationEquivalent c₂ c₃) :
    translationEquivalent c₁ c₃ := by
  rcases h₁₂ with ⟨hdegree₁₂, hrange₁₂, v, hsupport₁₂⟩
  rcases h₂₃ with ⟨hdegree₂₃, hrange₂₃, w, hsupport₂₃⟩
  refine ⟨hdegree₁₂.trans hdegree₂₃, hrange₁₂.trans hrange₂₃, ⟨v + w, ?_⟩⟩
  calc
    c₃.toPolymerSupport = c₂.toPolymerSupport.translate w := hsupport₂₃
    _ = (c₁.toPolymerSupport.translate v).translate w := by rw [hsupport₁₂]
    _ = c₁.toPolymerSupport.translate (v + w) := by
      rw [PolymerSupport.translate_translate]


end BoundedPolymerCase
end
end Exact3D
end StatMech
