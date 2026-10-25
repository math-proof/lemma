/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneBondwiseOrderedExploration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneExplorationSelector.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneOrderedDeterminedCut.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneActualSelectorSwitching.Part3
import Instance.StatisticalMechanics.Code.Sharpness.BackboneBondwiseOrderedExploration
open Finset
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

namespace BackboneDeterminedCutSwitching

open FluxEdgeCopy

open BackboneLabeledSwitching

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

variable {D : Type*}

theorem profileFlux_eq_of_outsideCopies_eq
    (m : G.edgeFinset -> Nat) (cut : Set (Sym2 V))
    (S T : Finset (FluxEdgeCopy.Copy G m))
    (hout : outsideCopies G m cut S = outsideCopies G m cut T)
    (e : G.edgeFinset) (he : e.1 ∉ cut) :
    profileFlux G m S e = profileFlux G m T e := by
  classical
  have hcard := congrArg
    (fun U : Finset (FluxEdgeCopy.Copy G m) =>
      #(U.filter (fun i : FluxEdgeCopy.Copy G m => i.1 = e))) hout
  have hfilter : ∀ U : Finset (FluxEdgeCopy.Copy G m),
      (outsideCopies G m cut U).filter
          (fun i : FluxEdgeCopy.Copy G m => i.1 = e) =
        U.filter (fun i : FluxEdgeCopy.Copy G m => i.1 = e) := by
    intro U
    ext i
    simp only [outsideCopies, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hiU, _⟩, hie⟩
      exact ⟨hiU, hie⟩
    · rintro ⟨hiU, hie⟩
      refine ⟨⟨hiU, ?_⟩, hie⟩
      simpa [endsM, hie] using he
  dsimp only at hcard
  rw [hfilter S, hfilter T] at hcard
  exact hcard


end BackboneDeterminedCutSwitching
end StatMech.Sharpness
