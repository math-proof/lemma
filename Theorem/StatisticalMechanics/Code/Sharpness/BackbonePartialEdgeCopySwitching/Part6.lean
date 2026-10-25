/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialEdgeCopySwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Sharpness.BackboneExplorationRealization.Part12
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Def.StatisticalMechanics.Code.Sharpness.BackbonePartialEdgeCopySwitching.Part9
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


theorem rawFiberMass_eq_labeledFiberMass
    (beta : Real) (J : Sym2 V -> Real)
    (m : G.edgeFinset -> Nat) (A : Finset V)
    (Q : (G.edgeFinset -> Nat) -> Prop) [DecidablePred Q] :
    rawFiberMass G beta J m A Q = labeledFiberMass G beta J m A Q := by
  classical
  unfold rawFiberMass labeledFiberMass
  rw [rawPredicateMass_eq_labeled G beta J m
    (fun k => sources G (ofEdgeFun G k) = A ∧ Q k)]
  have hsubtype :
      (∑ S : Finset (FluxEdgeCopy.Copy G m),
        if RandomCurrent.sources (endsM G m) S = A ∧
            Q (profileFlux G m S) then
          labeledWeight G beta J m S else 0) =
        ∑ S : Fiber G m A (fun S => Q (profileFlux G m S)),
          labeledWeight G beta J m S.1 := by
    rw [← Finset.sum_filter]
    apply Finset.sum_subtype
    intro S
    simp
  rw [← hsubtype]
  apply Finset.sum_congr rfl
  intro S _
  rw [FluxEdgeCopy.sources_eq]


theorem rawFiberMass_eq_of_labeledToggle
    (beta : Real) (J : Sym2 V -> Real)
    (m : G.edgeFinset -> Nat) (A C : Finset V)
    (P : Finset (FluxEdgeCopy.Copy G m))
    (hPsrc : RandomCurrent.sources (endsM G m) P = C)
    (Q R : (G.edgeFinset -> Nat) -> Prop)
    [DecidablePred Q] [DecidablePred R]
    (htransport : ∀ S,
      Q (profileFlux G m S) <-> R (profileFlux G m (S ∆ P))) :
    rawFiberMass G beta J m A Q =
      rawFiberMass G beta J m (A ∆ C) R := by
  rw [rawFiberMass_eq_labeledFiberMass G beta J m A Q,
    rawFiberMass_eq_labeledFiberMass G beta J m (A ∆ C) R]
  exact sum_labeledWeight_toggle G beta J m A C P hPsrc
    (fun S => Q (profileFlux G m S))
    (fun S => R (profileFlux G m S)) htransport

end BackboneLabeledSwitching
end
end StatMech.Sharpness
