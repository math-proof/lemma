/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.FrontierD.FiniteFirstReturn.Part6


namespace StatMech.FrontierD

noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem finiteFirstReturnOccurrencePoint_injective
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (states : List {a : A // selected a})
    (hstates : states.Nodup) :
    Function.Injective
      (finiteFirstReturnOccurrencePoint sigma selected states) := by
  rintro ⟨i, k⟩ ⟨j, l⟩ hpoint
  have hstate : states.get i = states.get j := by
    by_contra hne
    have hdisjoint := finiteFirstReturnSegment_disjoint sigma selected
      (states.get i) (states.get j) hne
    rw [List.disjoint_left] at hdisjoint
    apply hdisjoint
      (List.mem_ofFn.mpr ⟨k, rfl⟩)
    apply List.mem_ofFn.mpr
    refine ⟨l, ?_⟩
    exact hpoint.symm
  have hij : i = j := hstates.injective_get hstate
  subst j
  have hkl : k = l := by
    apply (List.nodup_ofFn.mp
      (finiteFirstReturnSegment_nodup sigma selected (states.get i)))
    exact hpoint
  subst l
  rfl

end
end StatMech.FrontierD
