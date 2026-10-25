/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.InhomogeneousProduct.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.ABGhostRegularity.Part7
import Theorem.StatisticalMechanics.Code.Sharpness.ABThermodynamicPassage
import Theorem.StatisticalMechanics.Code.Sharpness.ABInfiniteGhost.Part7
open Filter MeasureTheory Set SimpleGraph Topology
open scoped NNReal ENNReal


namespace StatMech

namespace Sharpness

open ConfigSpace RandomCurrent

variable {V : Type*}


variable {W : Type*}


noncomputable def abigGhostWindow [DecidableEq V] (S : Finset V) :
    Finset (Option V) :=
  S.image some ∪ {none}


noncomputable def abigGhostWindowEquiv [DecidableEq V] (S : Finset V) :
    Option S ≃ abigGhostWindow S :=
  Equiv.ofBijective
    (fun z => match z with
      | none => ⟨none, by simp [abigGhostWindow]⟩
      | some x => ⟨some (x : V), by simp [abigGhostWindow, x.property]⟩)
    ⟨by
      intro a b hab
      rcases a with _ | a <;> rcases b with _ | b <;> simp_all,
    by
      rintro ⟨z, hz⟩
      rcases z with _ | x
      · exact ⟨none, rfl⟩
      · have hx : x ∈ S := by simpa [abigGhostWindow] using hz
        exact ⟨some ⟨x, hx⟩, rfl⟩⟩

end Sharpness
end StatMech
