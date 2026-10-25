/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialEdgeCopySwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Sharpness.BackboneExplorationRealization.Part12
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Def.StatisticalMechanics.Code.Sharpness.BackbonePartialEdgeCopySwitching.Part7
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


theorem toggleEquiv_weight_preserving
    (beta : Real) (J : Sym2 V -> Real)
    (m : G.edgeFinset -> Nat) (A C : Finset V)
    (P : Finset (FluxEdgeCopy.Copy G m))
    (hPsrc : RandomCurrent.sources (endsM G m) P = C)
    (Q R : Finset (FluxEdgeCopy.Copy G m) -> Prop)
    (htransport : ∀ S, Q S <-> R (S ∆ P))
    (S : Fiber G m A Q) :
    labeledWeight G beta J m S.1 =
      labeledWeight G beta J m
        ((toggleEquiv G m A C P hPsrc Q R htransport S).1) := rfl


theorem sum_labeledWeight_toggle
    (beta : Real) (J : Sym2 V -> Real)
    (m : G.edgeFinset -> Nat) (A C : Finset V)
    (P : Finset (FluxEdgeCopy.Copy G m))
    (hPsrc : RandomCurrent.sources (endsM G m) P = C)
    (Q R : Finset (FluxEdgeCopy.Copy G m) -> Prop)
    [DecidablePred Q] [DecidablePred R]
    (htransport : ∀ S, Q S <-> R (S ∆ P)) :
    (∑ S : Fiber G m A Q, labeledWeight G beta J m S.1) =
      ∑ T : Fiber G m (A ∆ C) R, labeledWeight G beta J m T.1 := by
  rw [← Equiv.sum_comp (toggleEquiv G m A C P hPsrc Q R htransport)]
  apply Finset.sum_congr rfl
  intro S _
  exact toggleEquiv_weight_preserving G beta J m A C P hPsrc Q R htransport S


end BackboneLabeledSwitching
end
end StatMech.Sharpness
