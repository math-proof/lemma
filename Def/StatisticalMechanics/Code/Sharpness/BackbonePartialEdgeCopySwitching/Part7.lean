/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialEdgeCopySwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Sharpness.BackboneExplorationRealization.Part12
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Instance.StatisticalMechanics.Code.Sharpness.BackbonePartialEdgeCopySwitching.Part4
open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneLabeledSwitching

open FluxEdgeCopy

open RandomCurrent

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def toggleEquiv
    (m : G.edgeFinset -> Nat) (A C : Finset V)
    (P : Finset (FluxEdgeCopy.Copy G m))
    (hPsrc : RandomCurrent.sources (endsM G m) P = C)
    (Q R : Finset (FluxEdgeCopy.Copy G m) -> Prop)
    (htransport : ∀ S, Q S <-> R (S ∆ P)) :
    Fiber G m A Q ≃ Fiber G m (A ∆ C) R where
  toFun S := ⟨S.1 ∆ P, by
    constructor
    · rw [sources_symmDiff, S.2.1, hPsrc]
    · exact (htransport S.1).mp S.2.2⟩
  invFun T := ⟨T.1 ∆ P, by
    constructor
    · rw [sources_symmDiff, T.2.1, hPsrc,
        symmDiff_assoc, symmDiff_self, symmDiff_bot]
    · apply (htransport (T.1 ∆ P)).mpr
      simpa only [symmDiff_symmDiff_cancel_right] using T.2.2⟩
  left_inv S := by
    apply Subtype.ext
    simp only [symmDiff_symmDiff_cancel_right]
  right_inv T := by
    apply Subtype.ext
    simp only [symmDiff_symmDiff_cancel_right]


noncomputable def labeledWeight (beta : Real) (J : Sym2 V -> Real)
    (m : G.edgeFinset -> Nat)
    (_ : Finset (FluxEdgeCopy.Copy G m)) : Real :=
  weight G beta J (ofEdgeFun G m)

end BackboneLabeledSwitching
end
end StatMech.Sharpness
