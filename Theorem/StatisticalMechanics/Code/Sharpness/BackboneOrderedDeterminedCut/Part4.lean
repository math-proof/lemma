/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneOrderedDeterminedCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePartialEdgeCopySwitching.Part6
import Def.StatisticalMechanics.Code.Sharpness.BackboneOrderedDeterminedCut.Part4
open Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

namespace BackboneDeterminedCutSwitching

open FluxEdgeCopy

open BackboneLabeledSwitching

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem fluxEvent_toggle_iff
    (m : G.edgeFinset -> Nat) (cut : Set (Sym2 V))
    (Q : (G.edgeFinset -> Nat) -> Prop)
    (hQ : FluxEventOutsideCut G m cut Q)
    (S P : Finset (FluxEdgeCopy.Copy G m))
    (hP : SupportedInCut G m cut P) :
    Q (profileFlux G m S) <-> Q (profileFlux G m (S ∆ P)) := by
  apply hQ
  exact (outsideCopies_symmDiff_eq G m cut S P hP).symm


theorem rawFiberMass_eq_of_determinedCutToggle
    (beta : Real) (J : Sym2 V -> Real)
    (m : G.edgeFinset -> Nat) (A C : Finset V)
    (cut : Set (Sym2 V))
    (P : Finset (FluxEdgeCopy.Copy G m))
    (hPsrc : RandomCurrent.sources (endsM G m) P = C)
    (hPcut : SupportedInCut G m cut P)
    (Q : (G.edgeFinset -> Nat) -> Prop) [DecidablePred Q]
    (hQ : FluxEventOutsideCut G m cut Q) :
    rawFiberMass G beta J m A Q =
      rawFiberMass G beta J m (A ∆ C) Q := by
  apply rawFiberMass_eq_of_labeledToggle G beta J m A C P hPsrc Q Q
  intro S
  exact fluxEvent_toggle_iff G m cut Q hQ S P hPcut


theorem rawFiberMass_eq_of_orderedDeterminedToggle
    {E : Type*} [DecidableEq E]
    (T : shb_OrderedLocalTests E (Sym2 V)) (accepted : E)
    (beta : Real) (J : Sym2 V -> Real)
    (m : G.edgeFinset -> Nat) (A C : Finset V)
    (P : Finset (FluxEdgeCopy.Copy G m))
    (hPsrc : RandomCurrent.sources (endsM G m) P = C)
    (hPcut : SupportedInCut G m (T.determinedCut accepted) P)
    (Q : (G.edgeFinset -> Nat) -> Prop) [DecidablePred Q]
    (hQ : FluxEventOutsideCut G m (T.determinedCut accepted) Q) :
    rawFiberMass G beta J m A Q =
      rawFiberMass G beta J m (A ∆ C) Q :=
  rawFiberMass_eq_of_determinedCutToggle G beta J m A C
    (T.determinedCut accepted) P hPsrc hPcut Q hQ

end BackboneDeterminedCutSwitching
end
end StatMech.Sharpness
