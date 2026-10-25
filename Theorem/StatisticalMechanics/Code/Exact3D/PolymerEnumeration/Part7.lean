/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part9


namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace BoundedPolymerCase

theorem mem_boundedSupportOf {d R : ℕ} (P : PolymerSupport d)
    (hP : P.containedInBox R) (x : BoundedSite d R) :
    x ∈ boundedSupportOf P hP ↔ x.1 ∈ P := by
  classical
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, hxy⟩
    have hval : y.1 = x.1 := Subtype.ext_iff.mp hxy
    simpa [hval] using y.2
  · intro hx
    refine Finset.mem_image.mpr ?_
    refine ⟨⟨x.1, by simpa using hx⟩, by simp, ?_⟩
    ext i
    rfl


theorem boundedSupportOf_card {d R : ℕ} (P : PolymerSupport d)
    (hP : P.containedInBox R) :
    (boundedSupportOf P hP).card = P.carrier.card := by
  classical
  unfold boundedSupportOf
  rw [Finset.card_image_of_injective]
  · exact Finset.card_attach
  · intro x y hxy
    exact Subtype.ext (congrArg BoundedSite.val hxy)


end BoundedPolymerCase
end
end Exact3D
end StatMech
