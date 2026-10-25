/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdges.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.InhomogeneousFKG
import Theorem.StatisticalMechanics.Code.FK.RussoDerivativeBetaSum
import Theorem.StatisticalMechanics.Code.FK.FiniteEnergy.Part4
import Def.StatisticalMechanics.Code.FK.ActiveEdges
open scoped BigOperators
open Finset


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


@[simp] theorem extendActive_apply (ω : ConfigSpace G.edgeSet) (e : G.edgeSet) :
    extendActive G ω e.1 = ω e := by
  simp [extendActive, e.2]

theorem extendActive_sup (ω η : ConfigSpace G.edgeSet) :
    extendActive G (ω ⊔ η) = extendActive G ω ⊔ extendActive G η := by
  funext e
  by_cases he : e ∈ G.edgeSet <;> simp [extendActive, he]

theorem extendActive_inf (ω η : ConfigSpace G.edgeSet) :
    extendActive G (ω ⊓ η) = extendActive G ω ⊓ extendActive G η := by
  funext e
  by_cases he : e ∈ G.edgeSet <;> simp [extendActive, he]

theorem extendActive_setOpen (e : G.edgeSet) (ω : ConfigSpace G.edgeSet) :
    extendActive G (setOpen e ω) = setOpen e.1 (extendActive G ω) := by
  funext a
  by_cases ha : a = e.1
  · subst a
    simp [extendActive, e.2]
  · by_cases hG : a ∈ G.edgeSet
    · have hne : (⟨a, hG⟩ : G.edgeSet) ≠ e := by
        intro h
        exact ha (congrArg Subtype.val h)
      rw [setOpen_of_ne ha]
      simp [extendActive, hG, setOpen_of_ne hne]
    · simp [extendActive, hG, setOpen_of_ne ha]

theorem extendActive_setClosed (e : G.edgeSet) (ω : ConfigSpace G.edgeSet) :
    extendActive G (setClosed e ω) = setClosed e.1 (extendActive G ω) := by
  funext a
  by_cases ha : a = e.1
  · subst a
    simp [extendActive, e.2]
  · by_cases hG : a ∈ G.edgeSet
    · have hne : (⟨a, hG⟩ : G.edgeSet) ≠ e := by
        intro h
        exact ha (congrArg Subtype.val h)
      rw [setClosed_of_ne ha]
      simp [extendActive, hG, setClosed_of_ne hne]
    · simp [extendActive, hG, setClosed_of_ne ha]


end FK
end StatMech
