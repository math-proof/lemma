/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneOrderedDeterminedCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePartialEdgeCopySwitching.Part6
import Def.StatisticalMechanics.Code.Sharpness.BackboneOrderedDeterminedCut.Part2
open Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

namespace shb_OrderedLocalExploration

variable {D E B : Type*} [DecidableEq E]


@[simp] theorem selects_nil (X : shb_OrderedLocalExploration D E B)
    (omega : B -> Bool) (d : D) : X.Selects omega d [] := trivial

@[simp] theorem selects_cons (X : shb_OrderedLocalExploration D E B)
    (omega : B -> Bool) (d : D) (e : E) (es : List E) :
    X.Selects omega d (e :: es) <->
      (X.tests d).order.find? ((X.tests d).test omega) = some e ∧
        X.Selects omega (X.advance d e) es := Iff.rfl

@[simp] theorem traceCut_nil (X : shb_OrderedLocalExploration D E B)
    (d : D) : X.traceCut d [] = ∅ := rfl

@[simp] theorem traceCut_cons (X : shb_OrderedLocalExploration D E B)
    (d : D) (e : E) (es : List E) :
    X.traceCut d (e :: es) =
      (X.tests d).determinedCut e ∪ X.traceCut (X.advance d e) es := rfl


theorem selects_iff_of_agreeOn_traceCut
    (X : shb_OrderedLocalExploration D E B)
    (omega eta : B -> Bool) (d : D) (word : List E)
    (hagree : ∀ b ∈ X.traceCut d word, omega b = eta b) :
    X.Selects omega d word <-> X.Selects eta d word := by
  induction word generalizing d with
  | nil => simp
  | cons e es ih =>
      rw [selects_cons, selects_cons]
      have hhead : ∀ b ∈ (X.tests d).determinedCut e,
          omega b = eta b := by
        intro b hb
        exact hagree b (by simp [traceCut, hb])
      have htail : ∀ b ∈ X.traceCut (X.advance d e) es,
          omega b = eta b := by
        intro b hb
        exact hagree b (by simp [traceCut, hb])
      rw [(X.tests d).firstAccepted_iff_of_agreeOn_determinedCut
        omega eta e hhead, ih (X.advance d e) htail]

end shb_OrderedLocalExploration
end
end StatMech.Sharpness
