/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialP2Reindex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneBondwiseOrderedExploration.Part6
import Instance.StatisticalMechanics.Code.Sharpness.BackbonePartialP2Reindex.Part2
open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackbonePartialP2Reindex

open FluxEdgeCopy

open BackboneLabeledSwitching

open BackboneDeterminedCutSwitching

variable {D : Type*}

def PairContributes
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (m : G.edgeFinset -> Nat)
    (A C : Finset V)
    (Q₁ R₁ Q₂ R₂ : (G.edgeFinset -> Nat) -> Prop)
    [DecidablePred Q₁] [DecidablePred R₁]
    [DecidablePred Q₂] [DecidablePred R₂] : Prop :=
  rawSourcePairFiberMass G beta J m A Q₁ R₁ ≠ 0 ∨
    rawSourcePairFiberMass G beta J m (A ∆ C) Q₂ R₂ ≠ 0


end BackbonePartialP2Reindex
end
end StatMech.Sharpness
